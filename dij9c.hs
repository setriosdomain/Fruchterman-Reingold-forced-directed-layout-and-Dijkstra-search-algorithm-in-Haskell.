{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts #-}
{-
        Developed by: Nicolas Larrea
        email: clarreap@vub.ac.be
        First Assignment: functional programming.
-}
import Data.List (find,delete)
import Data.Char (isSpace)
import qualified Data.Map as Map
import Data.Map (fromList,fromListWith,(!),member,adjust,keys,Map)
import Debug.Trace (trace,traceShow)
import System.Random (RandomGen,randoms,mkStdGen)
import Text.Printf (printf)
--import System.Environment (getArgs)

-- /********************************************
-- g is the global type of the graph
-- n is the type of the node labels (must be unique)
-- e is the type of the edge labels
class Graph g n e | g -> n e where
      nodes :: g -> [n] -- enumeration of the nodes
      edge :: g -> (n,n) -> Maybe e -- returns an edge between two nodes (if any)
      empty :: g -- returns an empty graph insertNode :: g -> n -> g -- add a node to the given graph
      insertNode :: g -> n -> g -- add a node to the given graph
      insertEdge :: g -> (n,n) -> e -> g -- add an edge to the given graph
      --aditional methods will need
      edges :: g -> [(n,n,e)] -- enumeration of all the edges associated with their correponding nodes
      toMap :: g -> Map n [(n, e)] --Map representation of all the nodes and their edges.
      toList :: g -> [(n,[(n,e)])] --list representation of all the nodes and their edges.

-- /********************************************Adjacent Matrix Graphs
newtype Matrix e =  Mat [[Maybe e]] deriving (Show,Eq) -- adjacent matrix.
--type synonyms easy of use.
type MatI = Matrix Int
type MatC = Matrix Char
type MatB = Matrix Bool
type MatCI = Matrix (Char,Int)
type MatCF = Matrix (Char,Float)
--adjacent matrix graph representation.
instance Read e => Graph (Matrix e) Int e where
 nodes (Mat rows) = [n | (n, _) <- zip [1..] rows]
 edge (Mat rs) (r, c)= maybe Nothing f $ find (get r) $ zip [1..] rs where
  			 f (_, e) = maybe Nothing snd $ find(get c) $ zip[1..] e
                         get x (i, _) = i == x
 empty = Mat[]
              
 insertNode mat@(Mat rs) row = growRep row len where
 			       growRep r l |r > l = grow mat(r, 1) 
 				       	   |otherwise = rep r mat where
                               len = length rs
                               rep ri(Mat rs)=Mat $ map ins $ zip [1..] rs where
                                  ins (i,x) |i==ri = replicate len Nothing
                                            |otherwise = x
                                             
 insertEdge mat (r,c) e= valid r c where 
 	          valid r c | r<0 || c<0 = mat
                       	    | otherwise = insE $ grow mat (r,c) where
                  insE m@(Mat rs)=maybe mat f $ find(get r) $ zip [1..] rs where
                           f (index, r) = (Mat $ ins index (nRow r) m)
                           get x (i, _) = i == x
                           nRow row  = map gcol $ zip [1..] row
                           gcol (i, cell) |i == c = Just e
                                          |otherwise = cell
                           ins ix nr (Mat rs) = map grw $ zip [1..] rs where
                                       grw (i, rw) |i == ix = nr 
                                                   |otherwise=rw        
  --aditional methods will need
 edges mat = toListWith mat (\r c me acc ->  getL r c me acc) where
             getL r' c' myE ac= maybe ac (\e->(r',c',e):ac) myE
 toMap mat = dist (toListWith mat (\r c me ac -> (r,getL c me):ac)) where
              getL col myE = maybe [] (\e->[(col,e)]) myE
              dist = Map.fromListWith (++)
 toList mat = Map.toList $ toMap mat

--Matrix helper methods
toListWith:: Matrix e->(Int->Int->Maybe e->[b]->[b])->[b]--[row,[(col,e)]]
toListWith (Mat rows) f  = foldr g [] $ zip [1..] rows where
                           g (row, col) acc = addEds row col acc
		           addEds row col acc=foldr h acc  $ zip [1..] col where
                                  h (c, edge) acc = addEd row c edge acc
                                  addEd r' c' mybe acc = f r' c' mybe acc 
--the matrix will grow if needed.
grow:: Matrix e ->(Int,Int) -> Matrix e
grow (Mat[]) (r,c)= if(r<=0 || c<=0) then Mat[] else grow (Mat[[Nothing]]) (r,c) 
grow (Mat oRs) (r,c) = if valid then Mat oRs else growRC (length oRs) where
      valid = (mx<=(length oRs) || r< 0||c<0)
      mx = max r c
      growRC from = grRow (mx-from) $ grCol (mx-from) $ Mat oRs
      grCol n (Mat rs) = Mat $ map(\edgs->edgs ++ replicate n Nothing) rs
      grRow n (Mat rs) |n == 0 = Mat rs
                       |otherwise=grRow (n-1) $ Mat $ rs++[replicate mx Nothing]
--reads any readable edge.   
instance Read e => Read (Matrix e) where readsPrec _ s =  [(parseMatrix s,"")] 
parseMatrix:: Read e => String -> Matrix e
parseMatrix str = foldr f (Mat[]) (divRs str $ gDim str) where 
		  f sr acc = insRw sr acc
                  insRw sr (Mat rows) = Mat $ foldr g [] (words sr):rows
                  g s acc= (if trim s =="_" then Nothing else Just $ read s):acc
                  divRs input readBuf= parse input where 
			getRw row = unwords $ take readBuf $ words row
                        parse []= [] 
                        parse s = let tr = trim s
                                  in getRw tr:parse(drop(length $ getRw tr)tr)
                  gDim ix = gl $ takeWhile isTrue [1..] where
                  		 isTrue x = x*x <= (length $ words ix)
		                 gl [] = 0 
                                 gl s = last s

-- /********************************************Binary Tree Graphs
--binary search tree graph implementation. 
--Stores the nodes and their corresponding edges.
instance (Read e, Ord n, Read n) => Graph (BinMap n [(n, e)]) n e where 
 nodes binMap = map (\(node,_) -> node) $ toList binMap

 edge binMap@(Node _ _ _) (row, col) = maybe Nothing f $ search binMap row where
                                       f edges = getEg $ find g edges
                                       g (col', edge) = col == col'
      			               getEg maybeVal = maybe Nothing h maybeVal
                                       h (_,edge) = Just edge

 edge EmptyMap _ = Nothing
 empty = EmptyMap 
 insertEdge binMap (r, c) edge = insertWith (ins r c) (++) r [(c,edge)]  where
      				 ins n n' = append (append binMap n) n' 
                                 append bMap' nod = insertWith bMap' (++) nod []

 insertNode binMap node = addReplace binMap node [] 
 --aditional methods 
 edges binMap  = foldr f [] $ toList binMap where 
                 f (node, edges) acc = combine node edges acc
      		 combine n' edges' acc' = foldr g acc' edges' where
                 	g(n,e) ac= (n',n,e):ac

 toMap binMap = fromListWith (++) $ toList binMap

 toList (Node(key,value) l r) = (key,value):((toList l) ++ (toList r))
 toList EmptyMap = []
      
--binary search tree used by the graph.
data BinMap k v = EmptyMap | Node (k,v) (BinMap k v) (BinMap k v) deriving (Show, Eq)
--type synonyms
type MapIF = BinMap Int [(Int,Float)]
type MapIC = BinMap Int [(Int,Char)]
type MapSF = BinMap String [(String,Float)]
type MapCI = BinMap Char [(Char,Int)]
type MapCF = BinMap Char [(Char,Float)]
type MapI = BinMap Int [(Int,Int)]

addReplace :: Ord k => BinMap k v -> k -> v  -> BinMap k v
addReplace EmptyMap key value  = Node (key,value) EmptyMap EmptyMap
addReplace (Node (key',value') left right) key value 
  | key == key' = Node (key,value)  left right
  | key < key'  = Node (key',value') (addReplace left key value) right
  | key > key'  = Node (key',value') left $ addReplace right key value

search :: Ord k =>BinMap k v -> k-> Maybe v
search EmptyMap _  = Nothing
search (Node (key',value') left right) key
  | key == key' = Just value'
  | key < key'  = search left key 
  | key > key'  = search right key 

insertWith:: Ord k => BinMap k v -> (v -> v -> v) -> k -> v  ->  BinMap k v
insertWith binMap f key new  = maybe aRep g $ search binMap key where 
                               aRep = addReplace binMap key new
                               g org = addReplace binMap key $ f org new

--reads any readable edge.
instance (Read e,Ord n,Read n)=>Read(BinMap n [(n, e)]) where 
	readsPrec _ s=[(parseBinMap s,"")] 
parseBinMap:: (Read e, Ord n, Read n) => String -> (BinMap n [(n, e)])
parseBinMap = parseCommand.tryParse.words where
	      tryParse [] = []
              tryParse (nodes:edge:rest) = nodes:edge:(tryParse rest)
              tryParse (s:rest)  = tryParse rest
              parseCommand [] = EmptyMap
              parseCommand commands = addEgs commands EmptyMap where
	           addEgs (ns:e:rest) bm =let f=insertEdge bm (read ns) $ read e
                                          in addEgs rest f
                   addEgs [] bm = bm
                   addEgs (_:rest) bm = addEgs rest bm

-- /********************************************Dijkstra Algorythm             
{-
  dijkstra ((read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10" )::MapCI) 'b' 'e'

  dijkstra (insertEdge (insertEdge (insertEdge (insertEdge (insertEdge (insertEdge(insertEdge (insertEdge ((insertEdge empty (1,3) 3)::MatI) (3,2) 4) (3,4) 1) (4,7) 3) (7,6) 1) (2,6) 12) (6,9) 2)   (9,5) 3) (2,8) 8)  1 5

  dijkstra (read "_ 1 4 _ 2 _ 4 _ 8 _ 14 _ 12 1 _ 14 17 5 _ 1 _ _ _ 10 _ _ 11 _ _ _ _ 9 17 15 _ _ _ 1 3 _ _ 18 _ _ 9 _ _ 12 1 _ _ _ 2 _ _ _ _ 19 3 1 _ 13 _ _ 6 _ 12 17 _ _ 16 _ _ _ _ 6 _ _ 20 _ _ _ _ 8 _ 9 _ 21 _ _ _ _ 7 10 5 _"::MatI) 1 9
   
-}
--Dijkstra algorithm. Usually dijkstra computes all the shortest paths for all the
--edges. This implementation will abort once the target node has been found.
dijkstra::(Num e,Ord e,Show e,Graph g n e,Ord n,Show n,Eq n)=>g->n->n->Maybe [n]
dijkstra gr from to = dij nds (fromList $ foldr f base $ delete from nds) where 
                      base = [(from, (0,Nothing))]
                      grMap  = toMap gr
                      nds = keys grMap
                      f nd acc =(nd, (fromIntegral (maxBound::Int),Nothing)):acc
                      getRes q = getMaybe from to grMap (reverse $ g to) where
                             g x = x : maybe [] g (snd $ q ! x)
                      dij [] dMap = getRes dMap 
                      dij q dMap = dij getNextNode relaxEdges where
                          getNextNode = (if nod == to then [] else delete nod q)
                          relaxEdges = foldr relax dMap $ grMap ! nod
                          nod = snd $ foldr h (fst $ dMap ! head q,head q) q 
                          h key (v',k') = min ((fst $ dMap ! key) ,key) (v', k')
                          relax(eg,d)=(adjust(min(fst(dMap!nod)+d,Just nod))eg)
--helper function.
getMaybe:: (Num e, Ord n, Show n, Eq n)=> n->n-> Map n [(n, e)]->[n]->Maybe [n]                             
getMaybe from to gr path = toMaybe (cd1 && cd2) path where
                    cd1 = hasKeys from to gr
                    cd2=length (filter hasInPath path)>1 || from==to
                    hasKeys from to gr =  member from gr && member to gr
                    hasInPath x = x == from || x == to
                    toMaybe True path = Just path
                    toMaybe False _   = Nothing

-- ******************************************** Forced Directed Layout Algoritm (Fruchterman-Reingold)
{-
layout ((read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10")::MapCI)  (mkStdGen 10) (Rec{org=(0,0),width=10,height=10})
layout (read "1 2 3 4 _ 5 _ 7 8"::Matrix Int)  (mkStdGen 5) (Rec{org=(0,0),width=10,height=10})
-}

--The rectangle where to draw the output.
data LayoutRect=Rec{org::(Float,Float),
                    width::Float,height::Float} deriving Show
--Constants used by the attractive and repulsive force ecuations.
data Const= Const{layoutRec::LayoutRect, c::Float{-between 0 and 1-}, 
                  k::Float,k2::Float} deriving Show
--Temporal data type (vertex info) that stores the unbounded node
--positions(ux,uy),their displacements(dpX,dpY),and the edges(ed)
--for each node.
data VInfo n e = Vec{nd::n,ed::[(n,e)],uX::Float,uY::Float,
                     dpX::Float,dpY::Float} deriving (Show, Eq)

--Fruchterman-Reingold forced directed layout algorithm: outputs a list 
--of nodes and their positions inside a layout rectangle. The layout 
--rectangle is specified by the user, to indicate the bounds of the 
--area where to draw the graph.
layout::(Ord n,Eq e,Eq n,Show n,Show e,Num e,Graph g n e,RandomGen r)=>
        g->r->LayoutRect->[(n,Float,Float)]
layout gr r layoutR= transUnbd simul (getUnbRec simul) layoutR where
         simul = foldr forceLayout initVert [tempr,tempr - temprDecr..0] where
         forceLayout ntmpr vs =setUnbd (applyForces vs) ntmpr lgth
         applyForces vs = attForce(repForce vs const lgth) const
         initVert = zipWith f (toList gr) $ zip (fst rnds) $ snd rnds
         f (n,edges) (rnd,rnd') = Vec{nd=n,ed=edges,uX=rnd,uY=rnd',dpX=0,dpY=0}
         rnds = splitAt lgth $ take (lgth * 2) $ randoms r
         lgth = length $ nodes gr
         tempr = (width layoutR)/10.0
         temprDecr=tempr/numIter
         numIter = 50
         rect=layoutRec const
         getK=(c const)*sqrt((width rect)*(height rect))/(fromIntegral lgth)
         const=Const{layoutRec=layoutR,c=0.5,k= getK,k2 = getK * getK}
--calculates the repulsive forces between the vertices.
repForce::(Ord n,Eq e,Eq n,Show n,Show e,Num e)=>
          [VInfo n e]->Const->Int->[VInfo n e]
repForce vs cnst n =
           sumDp vs [(nd v,disp v v',nd v') |v<-vs,v'<-vs,v /= v'] [] where
           disp v1 v2 =(dx*frD,dy*frD) where 
                   dx = (uX v1)-(uX v2)
                   dy = (uY v1)-(uY v2)
                   frD = (k2 cnst)/(sqrt(dx*dx+dy*dy)*sqrt(dx*dx+dy*dy))
           sumDp [] [] r = reverse r
           sumDp v l r = sumDp (drop 1 v) ((drop (n-1)) l) f where
                   f = (getV (v !! 0) (take (n-1) l)):r 
                   getV (Vec n' e ux uy dx dy) l'= getVec where
                        getVec = let (drX, drY) =foldr g (dx,dy) l'
                                     g (_,(dX,dY),_) (dX',dY')=(dX+dX',dY+dY')
                                 in Vec{nd=n',ed=e,uX=ux,uY=uy,dpX=drX,dpY=drY}
--calculates the attractive forces between the vertices.
attForce::(Ord n,Eq e,Eq n,Show n,Show e,Num e)=>
          [VInfo n e]->Const->[VInfo n e]
attForce vs cns = sumDp (keys getMap) getMap  where
              getMap = fromList (map h vs)
              h vert@(Vec n _ _ _ _ _) = (n,vert)
              sumDp [] dmp' = Map.fold(\vert acc -> vert:acc) [] dmp'
              sumDp q dmp' = sumDp (drop 1 q) (adjEg (head q) dmp') where
                    adjEg nd dmp = foldr g dmp (ed (dmp ! nd)) where
                          g (n',eV) mp |nd/=n' = aV mp eV (dmp ! nd) $ dmp ! n'
                                       |otherwise = mp
                          aV m e v@(Vec n _ _ _ _ _) 
                             v'@(Vec n' _ _ _ _ _) = f where
                             f = let (nV,nV') = dispAttr v v' e cns
                                 in Map.insert n' nV' (Map.insert n nV m) 
--helper attractive force function.
dispAttr::(Ord n,Eq e,Eq n,Show n,Show e,Num e)=>
          VInfo n e->VInfo n e->e->Const->(VInfo n e,VInfo n e)
dispAttr v1@(Vec n e ux uy dx dy) 
         v2@(Vec n' e' ux' uy' dx' dy') edgWght cnst
         =(Vec n e ux uy (dx-tX) (dy-tY),
           Vec n' e' ux' uy' (dx'+tX) (dy'+tY))
         where ddx = (uX v1)-(uX v2)
               ddy = (uY v1)-(uY v2)
               delta = sqrt(ddx*ddx+ddy*ddy)*read(show edgWght)
               fa = (delta*delta)/(k cnst)
               faOD= fa/delta
               tX = ddx/faOD
               tY = ddy/faOD

--sets the unbounded positions for all vertices.
setUnbd::(Ord n,Eq e,Eq n,Show n,Show e,Num e)=>
         [VInfo n e]->Float->Int->[VInfo n e]
setUnbd vs tempr n = foldr buildUnbd [] vs where
                    buildUnbd v acc = (setUbdLoc v):acc where
                    setUbdLoc vt@(Vec n e ux uy dx dy)=Vec{nd=n,ed=e,
                                                           uX= ux + (unBdx vt),
                                                           uY= uy + (unBdy vt),
                                                           dpX=dx,dpY=dy}
                    unBdx v = ((dpX v)/(tDisp v)) * (min (tDisp v) tempr)
                    unBdy v = ((dpY v)/(tDisp v)) * (min (tDisp v) tempr)
                    tDisp v = sqrt((dpX v)*(dpX v) + (dpY v)*(dpY v))

--At the end of the algorithm this function is called to transform 
--the unbounded vertices contained in the unbounded rectangle to 
--vertices in the user specified layout rectangle.
transUnbd::(Ord n,Eq e,Eq n,Show n,Show e,Num e)=>
             [VInfo n e]->LayoutRect->LayoutRect-> [(n,Float,Float)]
transUnbd vs ur lr = foldr transform [] vs where
  transform (Vec n _ ux uy _ _) res= (n, fst xy, snd xy):res where
              xy = transf (ux,uy) ur lr where
  transf (x',y') (Rec (xo',yo') w' h') (Rec (xo,yo) w h) = (gX,gY) where
              gX = (w/w')*(x'-xo') + xo
              gY = (h/h')*(y'-yo') + yo
--gets the unbounded rectangle that contains all unbounded vertex 
--positions.
getUnbRec::(Ord n,Eq e,Eq n,Show n,Show e,Num e)=>
           [VInfo n e]->LayoutRect
getUnbRec vs = getRec $ foldr minmax base vs where
               minmax (Vec n e ux uy dx dy) (minX,minY,maxX,maxY)
                      =(min minX ux,min minY uy,max maxX ux,max maxY uy)
               getRec (x,y,mx,my) = Rec{org=(x,y),width=(mx-x),height=(my-y)}
               base =(0,0,0,0)

-- ******************************************** Generate Latex code for drawing graph.
{-
  putStr $ toPsP ((read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10 ('e','f') 4 ('f','g') 10 ('c','g') 11")::MapCI) (mkStdGen 10) 'b' 'g' (Rec{org=(0,0),width=10,height=10})

    putStr $ toPsP (read "_ 1 4 _ 2 _ 4 _ 8 _ 14 _ 12 1 _ 14 17 5 _ 1 _ _ _ 10 _ _ 11 _ _ _ _ 9 17 15 _ _ _ 1 3 _ _ 18 _ _ 9 _ _ 12 1 _ _ _ 2 _ _ _ _ 19 3 1 _ 13 _ _ 6 _ 12 17 _ _ 16 _ _ _ _ 6 _ _ 20 _ _ _ _ 8 _ 9 _ 21 _ _ _ _ 7 10 5 _"::MatI) (mkStdGen 10) 1 9 (Rec{org=(0,0),width=10,height=10})

    putStr $ toPsP ((read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10 ('e','f') 4 ('f','g') 10 ('c','g') 11 ('g','h') 2 ('f','h') 7 ('e','h') 20 ('f','j') 9 ('e','i') 12 ('f','i') 13 ('j','k') 2 ('h','l') 8 ('l','m') 5 ('m','n') 7")::MapCI) (mkStdGen 10) 'b' 'n' (Rec{org=(0,0),width=10,height=10})

-}
--generates latex code to represent the ouput of the Fruchterman-Reingold
--forced directed algorithm (colored in black). The result of the shortest 
--path calculated using the dijkstra algorithm is represented by red arrows.
toPsP::(Eq e,Show n,Show e,Ord n,Ord e,Num e,Graph g n e,RandomGen r)=>
       g->r->n->n->LayoutRect->String
toPsP gr r n n' layoRec = unlines (arrows circ)  where
          layoutVs = layout gr r layoRec --(Rec{org=(0,0),width=10,height=10})
          circ=genCircles layoutVs 0.07{-radius-}
          arrows l=maybe (f []) f (dijkstra gr n n') where
                 f paths = l ++ (genArrows gr n n' layoutVs paths)
--generates the edges (arrows) of the graph(black), and the result from the
--dijkstra algorithm(red).
genArrows::(Ord n,Eq n,Show n,Graph g n e)=>
           g->n->n->[(n,Float,Float)]->[n]->[String]
genArrows gr n n' vs nds = foldr lines [] (keys $ eMp) where
 eMp = edgeMap gr n n' nds where
 edgeMap gr n n' nds = insRed (fromList $ foldr f [] (edges gr)) where
             f (n,n',_) acc =if n/=n' then ((n,n'),"black"):acc else acc
             insRed mp = foldr g mp  (zip nds (drop 1 nds)) where
                    g (n1,n2) mr = Map.insert (n1,n2) "red" mr
 lines (n0,n) acc=("\\psline[linecolor="++eMp!(n0,n)++"]{->}\
                    \("++(showF(fst $ m!n0))++","++showF(snd $ m!n0)++") \
                    \("++showF(fst $ m!n)++","++showF(snd $ m!n)++")"):acc where
  m = fromList $ map(\(n,p,p')->(n,(p,p'))) vs
  showF=printf "%f"--no scientific notation
--generates the circles that represent the nodes of a graph.
genCircles::(Ord n,Eq n,Show n)=>[(n,Float,Float)]->Float ->[String]
genCircles vs r= foldr circles [] vs where
     circles (_,x,y) acc=("\\pscircle[linecolor=black]\
                          \("++showF(x)++","++showF(y)++"\
                          \){"++showF(r)++"}"):acc where
                           showF=printf "%f"--no scientific notation

-- ******************************************** Helper funtions for parsing.

trim :: String -> String
trim = trimSide. trimSide where trimSide = reverse . dropWhile isSpace 

deleteWhiteSpace:: String -> String
deleteWhiteSpace = foldr(\x acc -> if isSpace x then acc else x:acc) []













-- ******************************************** Documentation purpose only: examples of usage
{-

  --  ******How to read a matrix graph

   read "1 2 3 4 _ 5 _ 7 8"::Matrix Int
   read "1 2 3 4 _ 5 _ 7 8"::MatI
   (read "1 2 3 4 _ 5 _ 7 8"::Matrix Int)==( read "1 2 3 4 _ 5 _ 7 8"::MatI)
   read "('a',1) ('b',2) _ ('c',3)"::Matrix(Char, Int)
   read "('a',1) ('b',2) _ ('c',3)"::MatCI
   read "_ ('z',7) ('b',3) _ _ ('@',7) ('a',1) _ _"::MatCI
   read "False _ True _"::Matrix Bool
   read "False _ True _"::MatB
   read "('a',1.3) _ ('b',1.8) _"::MatCF
   read "_ _ 8 _ _ 6 _ 3 _"::MatI
   read "_ ('z',7) ('b',3) _ _ ('@',7) ('a',1) _ _"::MatCI
   read "_ 1 4 _ 2 _ 4 _ 8 _ 14 _ 12 1 _ 14 17 5 _ 1 _ _ _ 10 _ _ 11 _ _ _ _ 9 17 15 _ _ _ 1 3 _ _ 18 _ _ 9 _ _ 12 1 _ _ _ 2 _ _ _ _ 19 3 1 _ 13 _ _ 6 _ 12 17 _ _ 16 _ _ _ _ 6 _ _ 20 _ _ _ _ 8 _ 9 _ 21 _ _ _ _ 7 10 5 _"::MatI

   --  ******Usage of the matrix graph interface
   let gr = (insertEdge empty (1,3) 3)::MatI
   let gr' = (insertEdge (insertEdge (insertEdge (insertEdge (insertEdge (insertEdge(insertEdge (insertEdge gr (3,2) 4) (3,4) 1) (4,7) 3) (7,6) 1) (2,6) 12) (6,9) 2) (9,5) 3) (2,8) 8)
   edge gr' (9,5)
   edge gr' (900,5000)
 
   let mi = (insertNode empty 5)::MatI
   let mi' = insertEdge mi (2,3) 4
   let mi'' = insertEdge mi' (2,4) 5

   let mic = (insertNode empty 5)::MatCI
   let mic' = insertEdge mic (3,1) ('a',7) --inserts
   let mic'' = insertEdge mic' (1,5) ('b',55) --inserts
   let mic''' = insertEdge mic'' (10,10) ('c',3) --grows
   let mic'''' = insertEdge mic''' (3,2) ('d',79) --inserts
   nodes mic''''
   edges mic''''
   edge mic'''' (10,10)
   toList mic''''
   toMap mic'''' 

   let mc = (insertNode empty 5)::MatC
   let mc' = insertEdge mc (2,3) 'a'
   let mc'' = insertEdge mc' (2,4) 'b'
   let mc''' = insertEdge mc'' (5,1) 'b' 
   edges mc'''
   toMap mc'''
   toList mc'''

   toList (insertEdge ((insertEdge empty (1,3) 3)::MatI) (3,4) 1)

   let x = (insertEdge empty (10,10) ('c',3))::Matrix (Char, Int) --grows
   let x = (insertEdge empty (10,10) ('c',3))::MatCI --grows
   edge x (10,10)
   insertEdge x (7,5) ('a',89)
   edge (insertEdge x (7,5) ('a',89)) (7,5)

   edges (empty::Matrix Int)
   nodes (empty::MatI)
   (empty::MatI)

   --  ******Reading binary tree graph

   (read "(1,2) 'a' (2,3) 'b' (3,2) 'c'")::BinMap Int [(Int,Char)]
   (read "(1,2) 'a' (2,3) 'b' (3,2) 'c'")::MapIC
   ((insertEdge EmptyMap (3,2) 1.2)::BinMap Int [(Int, Float)]) == ((insertEdge EmptyMap (3,2) 1.2)::MapIF)
   (read "(1,1) 'a' (2,3) 'b' (3,3) 'c'")::MapIC
   (read "(\"a\",\"b\") 1.1 (\"b\",\"c\") 2.2 (\"c\",\"a\") 3.3" )::MapSF
   (read "('a','b') 1 ('b','c') 2 ('c','a') 3" )::BinMap Char [(Char,Int)]
   (read "('a','b') 1 ('b','c') 2 ('c','a') 3" )::MapCI
   (parseBinMap "(1,2) 'a' (2,3) 'b' (3,2) 'c'")::MapIC

   --  ******Usage binary tree graph interface

   let g = (insertEdge EmptyMap (3,2) 1.2)::BinMap Int [(Int, Float)]
   let g = (insertEdge EmptyMap (3,2) 1.2)::MapIF
   ((insertEdge EmptyMap (3,2) 1.2)::BinMap Int [(Int, Float)]) == ((insertEdge EmptyMap (3,2) 1.2)::MapIF)
   let g' = insertEdge g (3,4) 4.5
   let g'' = insertEdge (insertEdge g' (2,3) 3) (1,2) 21.8
   let g'''  = insertEdge (insertEdge g'' (1,3) 8) (4,1) 21.8
   edge g''' (3,4)
   edge g''' (4,11)

   let g = (insertEdge EmptyMap ("a","b") 1.2)::BinMap String [(String, Float)]
   let g2 = insertEdge (insertEdge g ("a","c") 4) ("c","d") 21.8
   let g = (insertEdge EmptyMap ('a','b') 1.2)::BinMap Char [(Char, Float)]
   (insertNode EmptyMap 2)::BinMap Int [(Int, Float)]
   toList (insertEdge ((insertEdge empty (1,3) 3)::MapI) (3,4) 1)

   --  ******Dijkstra algorythm examples.

   let g = (read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10" )::MapCI
   dijkstra g  'b' 'e'
   dijkstra ((read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10" )::MapCI) 'a' 'e'
   dijkstra ((read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10" )::MapCI) 'e' 'a'
   dijkstra ((read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10" )::MapCI) 'z' 't'
   dijkstra (read "_ 1 4 _ 2 _ 4 _ 8 _ 14 _ 12 1 _ 14 17 5 _ 1 _ _ _ 10 _ _ 11 _ _ _ _ 9 17 15 _ _ _ 1 3 _ _ 18 _ _ 9 _ _ 12 1 _ _ _ 2 _ _ _ _ 19 3 1 _ 13 _ _ 6 _ 12 17 _ _ 16 _ _ _ _ 6 _ _ 20 _ _ _ _ 8 _ 9 _ 21 _ _ _ _ 7 10 5 _"::MatI) 1 9
   dijkstra (read "_ 1 4 _ 2 _ 4 _ 8 _ 14 _ 12 1 _ 14 17 5 _ 1 _ _ _ 10 _ _ 11 _ _ _ _ 9 17 15 _ _ _ 1 3 _ _ 18 _ _ 9 _ _ 12 1 _ _ _ 2 _ _ _ _ 19 3 1 _ 13 _ _ 6 _ 12 17 _ _ 16 _ _ _ _ 6 _ _ 20 _ _ _ _ 8 _ 9 _ 21 _ _ _ _ 7 10 5 _"::MatI) 1 100

   --  ******Force directed layout (Fruchterman-Reingold) example.

   layout ((read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10")::MapCI)  (mkStdGen 10) (Rec{org=(0,0),width=100,height=100})

   layout (read "_ 1 4 _ 2 _ 4 _ 8 _ 14 _ 12 1 _ 14 17 5 _ 1 _ _ _ 10 _ _ 11 _ _ _ _ 9 17 15 _ _ _ 1 3 _ _ 18 _ _ 9 _ _ 12 1 _ _ _ 2 _ _ _ _ 19 3 1 _ 13 _ _ 6 _ 12 17 _ _ 16 _ _ _ _ 6 _ _ 20 _ _ _ _ 8 _ 9 _ 21 _ _ _ _ 7 10 5 _"::MatI) (mkStdGen 3) (Rec{org=(0,0),width=25,height=25})

   -- ******Generate latex code.

   putStr $ toPsP ((read "('a','c') 2 ('a','d') 6 ('b','a') 3 ('b','d') 8 ('c','d') 7 ('c','e') 5 ('d','e') 10")::MapCI) (mkStdGen 5) 'b' 'e'  (Rec{org=(0,0),width=11,height=11})

   putStr $ toPsP (read "_ 1 4 _ 2 _ 4 _ 8 _ 14 _ 12 1 _ 14 17 5 _ 1 _ _ _ 10 _ _ 11 _ _ _ _ 9 17 15 _ _ _ 1 3 _ _ 18 _ _ 9 _ _ 12 1 _ _ _ 2 _ _ _ _ 19 3 1 _ 13 _ _ 6 _ 12 17 _ _ 16 _ _ _ _ 6 _ _ 20 _ _ _ _ 8 _ 9 _ 21 _ _ _ _ 7 10 5 _"::MatI) (mkStdGen 10) 1 9  (Rec{org=(0,0),width=20,height=20})

-}





