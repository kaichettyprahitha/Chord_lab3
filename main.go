package main

import (
	"bufio"
	pb "chord/protocol"
	"context"
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"crypto/sha1"
	"encoding/base64"
	"flag"
	"fmt"
	"google.golang.org/grpc"
	"io"
	"log"
	"math/big"
	"net"
	"os"
	"strings"
	"sync"
	"time"
)

const (
	defaultSuccessorListSize = 3
	keySize                  = sha1.Size * 8
	maxLookupSteps           = 32
)

type Node struct {
	pb.UnimplementedChordServer
	mu            sync.RWMutex
	Address       string
	Port          string
	ID            string
	Predecessor   string
	Successors    []string
	FingerTable   []string
	numSuccessors int
}

type FileData struct {
	Content     string
	NodeID      string
	NodeAddress string
}

var (
	localAddress  string
	two           = big.NewInt(2)
	hashMod       = new(big.Int).Exp(big.NewInt(2), big.NewInt(keySize), nil)
	encryptionKey = []byte("passphrasewhichneedstobe32bytes!")
)

func init() {
	conn, err := net.Dial("udp", "8.8.8.8:80")
	if err != nil {
		log.Fatal(err)
	}
	defer conn.Close()

	localAddr := conn.LocalAddr().(*net.UDPAddr)
	localAddress = localAddr.IP.String()

	if localAddress == "" {
		panic("init: failed to find non-loopback interface with valid address on this node")
	}

	log.Printf("found local address %s\n", localAddress)
}

func main() {
	var ip, port, joinIp, joinPort, idOverride string
	var ts, tff, tcp, r int

	flag.StringVar(&ip, "a", "", "IP address of the node")
	flag.StringVar(&port, "p", "", "Port of the node")
	flag.StringVar(&joinIp, "ja", "", "Join an existing ring at given address")
	flag.StringVar(&joinPort, "jp", "", "Port to existing ring")
	flag.IntVar(&ts, "ts", 0, "Time between stabilizations")
	flag.IntVar(&tff, "tff", 0, "Time between fixing fingers")
	flag.IntVar(&tcp, "tcp", 0, "Time between checking predecessor")
	flag.IntVar(&r, "r", defaultSuccessorListSize, "Number of successors to maintain")
	flag.StringVar(&idOverride, "i", "", "Override ID for the node")

	flag.Parse()

	var node *Node
	var err error

	if ip == "" || port == "" {
		log.Fatal("IP and Port must be specified.")
	}

	if node, err = StartServer(ip, port, joinIp, joinPort, ts, tff, tcp, r, idOverride); err != nil {
		log.Fatal("Failed creating node: ", err)
	}

	shell(node)
}

func shell(node *Node) {
	log.Println("Starting interactive shell")
	in := bufio.NewScanner(os.Stdin)

	for in.Scan() {
		words := strings.Fields(in.Text())
		if len(words) == 0 {
			continue
		}

		switch words[0] {
		case "StoreFile":
			if len(words) != 2 {
				log.Println("Usage: StoreFile <input_file>")
				continue
			}
			inputFileName := words[1]
			node.storeFile(inputFileName)

		case "LookUp":
			if len(words) != 2 {
				log.Println("Usage: LookUp <file_name>")
				continue
			}
			fileName := words[1]
			node.lookUp(fileName)

		case "PrintState":
			if len(words) != 1 {
				log.Println("Usage: PrintState")
				continue
			}
			node.dump()

		case "Quit":
			if len(words) != 1 {
				log.Println("Usage: Quit")
				continue
			}
			os.Exit(0)

		case "Ping":
			if len(words) != 2 {
				log.Println("Usage: Ping <address>")
				continue
			}
			address := words[1]
			node.ping(address)
		}
	}
}

func (node *Node) dump() {
	node.mu.RLock()
	defer node.mu.RUnlock()

	log.Println()
	log.Print("dump: information about this node")

	log.Print("Neighborhood")
	log.Print("pred:   ", addr(node.Predecessor))
	log.Print("self:   ", addr(node.Address))
	for i, succ := range node.Successors {
		log.Printf("succ %d: %s", i, addr(succ))
	}

	log.Println()
	log.Print("Finger table")
	nodeId := hash(node.Address)

	log.Printf("Node ID: %040x", nodeId)

	for i := 1; i <= keySize && node.FingerTable[i] != ""; i++ {
		start := jump(node.Address, i)

		exp := new(big.Int).SetInt64(int64(i))
		power := new(big.Int).Exp(two, exp, nil)
		end := new(big.Int).Add(nodeId, power)
		end.Mod(end, hashMod)

		log.Printf(" [%3d]: %s \t[%040x -> %040x)",
			i,
			addr(node.FingerTable[i]),
			start,
			end)
	}

	log.Println()
	log.Print("Data items")
	storageDir := fmt.Sprintf("storage/%s", node.Port)
	files, err := os.ReadDir(storageDir)
	if err != nil {
		if !os.IsNotExist(err) {
			log.Printf("Error reading storage directory: %v", err)
		}
		log.Println()
		return
	}

	for _, file := range files {
		if !file.IsDir() {
			filePath := fmt.Sprintf("%s/%s", storageDir, file.Name())
			content, err := os.ReadFile(filePath)
			if err != nil {
				log.Printf("Error reading file %s: %v", file.Name(), err)
				continue
			}
			s := fmt.Sprintf("%040x", hash(file.Name()))
			log.Printf("    %s.. %s => %s", s[:8], file.Name(), string(content))
		}
	}
	log.Println()
}

func jump(address string, fingerentry int) *big.Int {
	n := hash(address)
	exp := new(big.Int).SetInt64(int64(fingerentry - 1))
	power := new(big.Int).Exp(two, exp, nil)

	sum := new(big.Int).Add(n, power)
	return new(big.Int).Mod(sum, hashMod)
}
func (node *Node) fixFingers(next int) int {
	if next > keySize {
		return 1
	}

	_, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()

	nodeId := hash(node.Address)
	exp := new(big.Int).SetInt64(int64(next - 1))
	power := new(big.Int).Exp(two, exp, nil)
	target := new(big.Int).Add(nodeId, power)
	target.Mod(target, hashMod)

	found, nextNode := node.findSuccessor(target)
	var successor string

	if !found {
		var err error
		successor, err = node.find(target, nextNode)
		if err != nil {
			log.Printf("fixFingers: failed to find successor for finger %d: %v", next, err)
			return next + 1
		}
	} else {
		successor = nextNode
	}

	//if err := ping_rpc(ctx, successor, node.Address); err != nil {
	//	log.Printf("fixFingers: finger %d successor %s appears dead", next, successor)
	//	return next + 1
	//}

	node.mu.Lock()
	node.FingerTable[next] = successor
	node.mu.Unlock()

	return next + 1
}

func encrypt(data []byte) (string, error) {
	block, err := aes.NewCipher(encryptionKey)
	if err != nil {
		return "", err
	}

	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return "", err
	}

	nonce := make([]byte, gcm.NonceSize())
	if _, err := io.ReadFull(rand.Reader, nonce); err != nil {
		return "", err
	}

	ciphertext := gcm.Seal(nonce, nonce, data, nil)

	return base64.StdEncoding.EncodeToString(ciphertext), nil
}

func decrypt(encryptedData string) ([]byte, error) {
	data, err := base64.StdEncoding.DecodeString(encryptedData)
	if err != nil {
		return nil, err
	}

	block, err := aes.NewCipher(encryptionKey)
	if err != nil {
		return nil, err
	}

	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return nil, err
	}

	if len(data) < gcm.NonceSize() {
		return nil, fmt.Errorf("malformed ciphertext")
	}

	return gcm.Open(nil,
		data[:gcm.NonceSize()],
		data[gcm.NonceSize():],
		nil,
	)
}

func (node *Node) lookUp(fileName string) {
	fileKey := hash(fileName)
	found, successorAddr := node.findSuccessor(fileKey)
	var responsibleNode string
	var err error

	if !found {
		responsibleNode, err = node.find(fileKey, successorAddr)
		if err != nil {
			log.Printf("Lookup failed: %v", err)
			return
		}
	} else {
		responsibleNode = successorAddr
	}

	fileData, content, err := node.tryGetFile(responsibleNode, fileName)
	if err != nil {
		fileData, content, err = node.tryReplicaNodes(fileName)
		if err != nil {
			fmt.Printf("File not found or all replicas failed: %v\n", err)
			return
		}
	}

	fmt.Printf("File found at node %s (%s)\nContents: %s\n",
		fileData.NodeID, fileData.NodeAddress, content)
}

func (node *Node) lookUpFileLocally(fileName string) (*FileData, string, error) {
	filePath := fmt.Sprintf("storage/%s/%s", node.Port, fileName)
	encryptedContent, err := os.ReadFile(filePath)

	if err != nil {
		if os.IsNotExist(err) {
			return nil, "", fmt.Errorf("file not found")
		}
		return nil, "", fmt.Errorf("error reading file: %v", err)
	}

	decryptedContent, err := decrypt(string(encryptedContent))
	if err != nil {
		return nil, "", fmt.Errorf("error decrypting file: %v", err)
	}

	fileData := &FileData{
		NodeID:      node.ID,
		NodeAddress: node.Address,
	}

	return fileData, string(decryptedContent), nil
}

func (node *Node) GetFile(ctx context.Context, req *pb.GetFileRequest) (*pb.GetFileResponse, error) {
	fileData, content, err := node.lookUpFileLocally(req.FileName)
	if err != nil {
		if err.Error() == "file not found" {
			return &pb.GetFileResponse{Found: false}, nil
		}
		return nil, err
	}

	return &pb.GetFileResponse{
		Found:       true,
		Content:     content,
		NodeId:      fileData.NodeID,
		NodeAddress: fileData.NodeAddress,
	}, nil
}

func (node *Node) storeFile(inputFileName string) {
	content, err := os.ReadFile(inputFileName)
	if err != nil {
		log.Printf("Failed to read file %s: %v", inputFileName, err)
		return
	}

	fileKey := hash(inputFileName)
	found, successorAddr := node.findSuccessor(fileKey)
	var responsibleNode string

	if !found {
		responsibleNode, err = node.find(fileKey, successorAddr)
		if err != nil {
			log.Printf("Failed to find responsible node: %v", err)
			return
		}
	} else {
		responsibleNode = successorAddr
	}

	if responsibleNode == node.Address {
		err = node.storeFileLocally(inputFileName, string(content))
		if err != nil {
			log.Printf("Failed to store file locally: %v", err)
			return
		}
		fmt.Printf("File stored successfully at node %s (%s)\n",
			node.ID, node.Address)
		return
	}

	conn, err := grpc.Dial(responsibleNode, grpc.WithInsecure())
	if err != nil {
		log.Printf("Failed to connect to responsible node: %v", err)
		return
	}
	defer conn.Close()

	client := pb.NewChordClient(conn)
	_, err = client.StoreFile(context.Background(), &pb.StoreFileRequest{
		FileName: inputFileName,
		Content:  string(content),
	})

	if err != nil {
		log.Printf("Failed to store file: %v", err)
		return
	}

	fmt.Printf("File stored successfully on node %s\n", responsibleNode)
}

func (node *Node) storeFileLocally(fileName, content string) error {
	encryptedContent, err := encrypt([]byte(content))
	if err != nil {
		return fmt.Errorf("failed to encrypt content: %v", err)
	}

	storageDir := fmt.Sprintf("storage/%s", node.Port)
	err = os.MkdirAll(storageDir, 0755)
	if err != nil {
		return fmt.Errorf("failed to create storage directory: %v", err)
	}

	filePath := fmt.Sprintf("%s/%s", storageDir, fileName)
	err = os.WriteFile(filePath, []byte(encryptedContent), 0644)
	if err != nil {
		return fmt.Errorf("failed to write file to disk: %v", err)
	}

	return nil
}

func (node *Node) StoreFile(ctx context.Context, req *pb.StoreFileRequest) (*pb.StoreFileResponse, error) {
	fileKey := hash(req.FileName)
	found, successorAddr := node.findSuccessor(fileKey)

	if found && successorAddr != node.Address {
		conn, err := grpc.Dial(successorAddr, grpc.WithInsecure())
		if err != nil {
			return nil, fmt.Errorf("failed to connect to responsible node: %v", err)
		}
		defer conn.Close()

		client := pb.NewChordClient(conn)
		return client.StoreFile(ctx, req)
	}

	err := node.replicateFile(req.FileName, req.Content, 0)
	if err != nil {
		return &pb.StoreFileResponse{Success: false}, err
	}

	return &pb.StoreFileResponse{Success: true}, nil
}

func (node *Node) findSuccessor(id *big.Int) (bool, string) {
	node.mu.RLock()
	defer node.mu.RUnlock()

	if len(node.Successors) == 0 {
		return true, node.Address
	}

	successor := node.Successors[0]

	if between(hash(node.Address), id, hash(successor), true) {
		return true, successor
	}

	nextNode := node.closestPrecedingNode(id)
	return false, nextNode
}

func (node *Node) closestPrecedingNode(id *big.Int) string {
	for i := keySize; i >= 1; i-- {
		finger := node.FingerTable[i]
		if finger == "" {
			continue
		}

		fingerHash := hash(finger)
		if between(hash(node.Address), fingerHash, id, false) {
			_, cancel := context.WithTimeout(context.Background(), time.Second)
			defer cancel()
			//if err := ping_rpc(ctx, finger, node.Address); err == nil {
			//	return finger
			//}
			return finger
		}
	}

	if len(node.Successors) > 0 {
		return node.Successors[0]
	}

	return node.Address
}

func (node *Node) find(id *big.Int, start string) (string, error) {
	nextNode := start
	visited := make(map[string]bool)
	steps := 0

	for steps < maxLookupSteps {
		if visited[nextNode] {
			return "", fmt.Errorf("routing loop detected while searching for %s", id.String())
		}
		visited[nextNode] = true

		conn, err := grpc.Dial(nextNode, grpc.WithInsecure())
		if err != nil {
			return "", fmt.Errorf("failed to connect to node %s: %v", nextNode, err)
		}
		defer conn.Close()

		client := pb.NewChordClient(conn)
		response, err := client.FindSuccessor(context.Background(), &pb.FindSuccessorRequest{Id: id.String()})
		if err != nil {
			return "", fmt.Errorf("failed to find successor from node %s: %v", nextNode, err)
		}

		if response.Found {
			return response.NextNode, nil
		}
		nextNode = response.NextNode
		steps++
	}

	return "", fmt.Errorf("exceeded maximum lookup steps (%d) while searching for %s", node.numSuccessors, id.String())
}

func (node *Node) FindSuccessor(ctx context.Context, in *pb.FindSuccessorRequest) (*pb.FindSuccessorResponse, error) {
	//log.Println("Inside FindSuccessor: ", in.Id)
	id := new(big.Int)
	id.SetString(in.Id, 10)

	found, nextNode := node.findSuccessor(id)
	return &pb.FindSuccessorResponse{
		Found:    found,
		NextNode: nextNode,
	}, nil
}

func ping_rpc(ctx context.Context, addr, selfAddr string) error {
	//if addr == "" || addr == selfAddr {
	//	return nil
	//}
	conn, err := grpc.Dial(addr, grpc.WithInsecure())
	if err != nil {
		return err
	}
	defer conn.Close()

	client := pb.NewChordClient(conn)

	_, err = client.Ping(ctx, &pb.PingRequest{})
	return err
}

func (node *Node) Ping(ctx context.Context, in *pb.PingRequest) (*pb.PingResponse, error) {
	return &pb.PingResponse{}, nil
}

func (node *Node) ping(address string) {
	fmt.Println("Ping: ", address)
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()

	err := ping_rpc(ctx, address, node.Address)
	if err != nil {
		log.Printf("Ping to %s failed: %v", address, err)
	} else {
		log.Printf("Ping to %s succeeded", address)
	}
}

func (node *Node) join(ip, port string, joined chan bool) {
	address := net.JoinHostPort(ip, port)

	successorAddress, err := node.find(hash(node.Address), address)

	if err != nil {
		log.Fatalf("join: failed to find successor: %v", err)
	}

	node.mu.Lock()
	node.Successors = []string{successorAddress}
	node.mu.Unlock()

	fmt.Printf("Join: Set %s as successor\n", successorAddress)
	joined <- true
}

func StartServer(ip, port, joinIp, joinPort string, ts, tff, tcp, r int, idOverride string) (*Node, error) {
	address := net.JoinHostPort(ip, port)

	var nodeID string
	if idOverride != "" {
		nodeID = idOverride
	} else {
		nodeID = fmt.Sprintf("%040x", hash(address))
	}

	node := &Node{
		Address:       address,
		Port:          port,
		ID:            nodeID,
		FingerTable:   make([]string, keySize+1),
		Predecessor:   "",
		Successors:    nil,
		numSuccessors: r,
	}

	joined := make(chan bool)

	if joinIp == "" || joinPort == "" {
		log.Print("StartServer: creating new ring")

		node.Successors = []string{node.Address}
		go func() {
			joined <- true
		}()

	} else {
		go node.join(joinIp, joinPort, joined)
	}

	grpcServer := grpc.NewServer()
	pb.RegisterChordServer(grpcServer, node)

	list, err := net.Listen("tcp", node.Address)

	if err != nil {
		log.Fatalf("failed to listen: %v", err)
	}
	log.Printf("listening on %s", node.Address)

	<-joined

	go func() {
		if err := grpcServer.Serve(list); err != nil {
			log.Fatalf("failed to serve: %v", err)
		}
	}()

	go func() {
		for {
			time.Sleep(time.Duration(ts/1000) * time.Second)
			node.stabilize()
		}
	}()
	go func() {
		nextFinger := 0
		for {
			time.Sleep(time.Duration(tff/1000) * time.Second)
			nextFinger = node.fixFingers(nextFinger)
		}
	}()
	go func() {
		for {
			time.Sleep(time.Duration(tcp/1000) * time.Second)
			node.checkPredecessor()
		}
	}()

	return node, nil
}

func (node *Node) checkPredecessor() {
	node.mu.RLock()
	predecessor := node.Predecessor
	node.mu.RUnlock()

	if predecessor != "" && predecessor != node.Address {
		ctx, cancel := context.WithTimeout(context.Background(), time.Second)
		defer cancel()

		if err := ping_rpc(ctx, predecessor, node.Address); err != nil {
			node.mu.Lock()
			node.Predecessor = ""
			node.mu.Unlock()
			log.Printf("checkPredecessor: predecessor %s has failed", predecessor)
		}
	}
}

func (node *Node) stabilize() {
	node.mu.RLock()
	if len(node.Successors) == 0 {
		node.mu.RUnlock()
		node.mu.Lock()
		node.Successors = []string{node.Address}
		node.mu.Unlock()
		return
	}
	successor := node.Successors[0]
	node.mu.RUnlock()

	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()

	if err := ping_rpc(ctx, successor, node.Address); err != nil {
		log.Printf("stabilize: successor %s appears to be dead", successor)
		node.handleSuccessorFailure()
		return
	}

	conn, err := grpc.Dial(successor, grpc.WithInsecure())
	if err != nil {
		log.Printf("stabilize: failed to connect to successor %s: %v", successor, err)
		node.handleSuccessorFailure()
		return
	}
	defer conn.Close()

	client := pb.NewChordClient(conn)
	response, err := client.GetPredecessorAndSuccessors(ctx, &pb.GetPredecessorAndSuccessorsRequest{})
	if err != nil {
		log.Printf("stabilize: failed to get predecessor: %v", err)
		node.handleSuccessorFailure()
		return
	}

	x := response.Predecessor

	if x != "" && x != node.Address {
		if between(hash(node.Address), hash(x), hash(successor), false) {
			if err := ping_rpc(ctx, x, node.Address); err == nil {
				node.mu.Lock()
				node.Successors[0] = x
				successor = x
				node.mu.Unlock()

				conn, err = grpc.Dial(successor, grpc.WithInsecure())
				if err != nil {
					log.Printf("stabilize: failed to connect to new successor %s: %v", successor, err)
					return
				}
				defer conn.Close()
				client = pb.NewChordClient(conn)
			}
		}
	}

	_, err = client.Notify(ctx, &pb.NotifyRequest{Candidate: node.Address})
	if err != nil {
		log.Printf("stabilize: failed to notify successor: %v", err)
		return
	}

	newSuccessors := append([]string{successor}, response.Successors...)
	uniqueSuccessors := make(map[string]bool)
	finalSuccessors := []string{}

	for _, succ := range newSuccessors {
		if !uniqueSuccessors[succ] && succ != node.Address {
			if err := ping_rpc(ctx, succ, node.Address); err == nil {
				uniqueSuccessors[succ] = true
				finalSuccessors = append(finalSuccessors, succ)
			}
		}
	}

	if len(finalSuccessors) == 0 {
		finalSuccessors = []string{node.Address}
	}

	if len(finalSuccessors) > node.numSuccessors {
		finalSuccessors = finalSuccessors[:node.numSuccessors]
	}

	node.mu.Lock()
	node.Successors = finalSuccessors
	node.FingerTable[1] = finalSuccessors[0]
	node.mu.Unlock()
}

func (node *Node) GetPredecessorAndSuccessors(ctx context.Context, in *pb.GetPredecessorAndSuccessorsRequest) (*pb.GetPredecessorAndSuccessorsResponse, error) {
	node.mu.RLock()
	defer node.mu.RUnlock()

	return &pb.GetPredecessorAndSuccessorsResponse{
		Predecessor: node.Predecessor,
		Successors:  node.Successors,
	}, nil
}

func (node *Node) handleSuccessorFailure() {
	node.mu.Lock()
	defer node.mu.Unlock()

	for i := 1; i < len(node.Successors); i++ {
		successor := node.Successors[i]

		ctx, cancel := context.WithTimeout(context.Background(), time.Second)
		defer cancel()

		if err := ping_rpc(ctx, successor, node.Address); err == nil {
			node.Successors = append([]string{successor}, node.Successors[i+1:]...)
			log.Printf("handleSuccessorFailure: successfully switched to backup successor %s", successor)
			return
		}
	}

	if len(node.Successors) <= 1 || node.Successors[0] == node.Address {
		node.Successors = []string{node.Address}
		node.Predecessor = ""
		log.Printf("handleSuccessorFailure: no live successors found, becoming sole node")
		return
	}
}

func addr(a string) string {
	if a == "" {
		return "(empty)"
	}
	s := fmt.Sprintf("%040x", hash(a))
	return s[:8] + ".. (" + a + ")"
}

func (node *Node) notify(candidate string) {
	node.mu.Lock()
	defer node.mu.Unlock()
	if node.Predecessor == "" ||
		node.Predecessor == node.Address ||
		between(hash(node.Predecessor), hash(candidate), hash(node.Address), false) {
		node.Predecessor = candidate
	}
}

func (node *Node) Notify(ctx context.Context, in *pb.NotifyRequest) (*pb.NotifyResponse, error) {
	candidate := in.Candidate

	node.notify(candidate)

	return &pb.NotifyResponse{}, nil
}

func hash(elt string) *big.Int {
	hasher := sha1.New()
	hasher.Write([]byte(elt))
	return new(big.Int).SetBytes(hasher.Sum(nil))
}

func between(start, elt, end *big.Int, inclusive bool) bool {
	if end.Cmp(start) > 0 {
		return (start.Cmp(elt) < 0 && elt.Cmp(end) < 0) || (inclusive && elt.Cmp(end) == 0)
	} else {
		return start.Cmp(elt) < 0 || elt.Cmp(end) < 0 || (inclusive && elt.Cmp(end) == 0)
	}
}

func (node *Node) replicateFile(fileName, content string, hopCount int) error {
	if hopCount >= node.numSuccessors {
		return nil
	}

	err := node.storeFileLocally(fileName, content)
	if err != nil {
		return fmt.Errorf("failed to store file locally during replication: %v", err)
	}

	node.mu.RLock()
	if len(node.Successors) <= hopCount {
		node.mu.RUnlock()
		return nil
	}
	nextSuccessor := node.Successors[hopCount]
	node.mu.RUnlock()

	if nextSuccessor == node.Address {
		return nil
	}

	conn, err := grpc.Dial(nextSuccessor, grpc.WithInsecure())
	if err != nil {
		return fmt.Errorf("failed to connect to successor for replication: %v", err)
	}
	defer conn.Close()

	client := pb.NewChordClient(conn)
	_, err = client.ReplicateFile(context.Background(), &pb.ReplicateFileRequest{
		FileName: fileName,
		Content:  content,
		HopCount: int32(hopCount + 1),
	})

	return err
}

func (node *Node) ReplicateFile(ctx context.Context, req *pb.ReplicateFileRequest) (*pb.ReplicateFileResponse, error) {
	err := node.replicateFile(req.FileName, req.Content, int(req.HopCount))
	if err != nil {
		return &pb.ReplicateFileResponse{Success: false}, err
	}
	return &pb.ReplicateFileResponse{Success: true}, nil
}

func (node *Node) tryGetFile(targetNode string, fileName string) (*FileData, string, error) {
	if targetNode == node.Address {
		return node.lookUpFileLocally(fileName)
	}

	conn, err := grpc.Dial(targetNode, grpc.WithInsecure())
	if err != nil {
		return nil, "", err
	}
	defer conn.Close()

	client := pb.NewChordClient(conn)
	resp, err := client.GetFile(context.Background(), &pb.GetFileRequest{FileName: fileName})
	if err != nil {
		return nil, "", err
	}

	if !resp.Found {
		return nil, "", fmt.Errorf("file not found")
	}

	return &FileData{
		NodeID:      resp.NodeId,
		NodeAddress: resp.NodeAddress,
	}, resp.Content, nil
}

func (node *Node) tryReplicaNodes(fileName string) (*FileData, string, error) {
	node.mu.RLock()
	successors := make([]string, len(node.Successors))
	copy(successors, node.Successors)
	node.mu.RUnlock()

	for _, successor := range successors {
		fileData, content, err := node.tryGetFile(successor, fileName)
		if err == nil {
			return fileData, content, nil
		}
	}

	return nil, "", fmt.Errorf("all replicas failed")
}
