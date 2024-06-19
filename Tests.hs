import Test.HUnit
import Challenges

testcalcBBInteractions1 = TestCase (assertEqual "For calcBBInteractions 8 [ (2,3) , (7,3) , (4,6) , (7,8) ], " 
    [((North,1),Path (West,2)),((North,2),Absorb),
    ((North,3),Path (North,6)),((North,4),Absorb),
    ((North,5),Path (East,5)),((North,6),Path (North,3)),
    ((North,7),Absorb),((North,8),Path (East,2)),
    ((East,1),Path (West,1)),((East,2),Path (North,8)),
    ((East,3),Absorb),((East,4),Path (East,7)),
    ((East,5),Path (North,5)),((East,6),Absorb),
    ((East,7),Path (East,4)),((East,8),Absorb),
    ((South,1),Path (West,4)),((South,2),Absorb),
    ((South,3),Path (West,7)),((South,4),Absorb),
    ((South,5),Path (West,5)),((South,6),Reflect),
    ((South,7),Absorb),((South,8),Reflect),
    ((West,1),Path (East,1)),((West,2),Path (North,1)),
    ((West,3),Absorb),((West,4),Path (South,1)),
    ((West,5),Path (South,5)),((West,6),Absorb),
    ((West,7),Path (South,3)),((West,8),Absorb)] 
    (calcBBInteractions 8 [ (2,3) , (7,3) , (4,6) , (7,8) ]))

testcalcBBInteractions2 = TestCase (assertEqual "For calcBBInteractions 8 [(1, 3), (3, 4), (7, 7), (3, 7)], " 
    [((North,1),Absorb),((North,2),Path (East,2)),
    ((North,3),Absorb),((North,4),Absorb),((North,5),Path (South,5)),
    ((North,6),Path (East,5)),((North,7),Absorb),((North,8),Path (East,6)),
    ((East,1),Path (West,1)),((East,2),Path (North,2)),
    ((East,3),Path (North,4)),((East,4),Absorb),((East,5),Path (North,6)),
    ((East,6),Path (North,8)),((East,7),Absorb),((East,8),Path (South,8)),
    ((South,1),Absorb),((South,2),Path (West,8)),((South,3),Absorb),
    ((South,4),Path (South,6)),((South,5),Path (North,5)),((South,6),Path (South,4)),
    ((South,7),Absorb),((South,8),Path (East,8)),((West,1),Path (East,1)),
    ((West,2),Reflect),((West,3),Absorb),((West,4),Reflect),((West,5),Path (West,6)),
    ((West,6),Path (West,5)),((West,7),Absorb),((West,8),Path (South,2))] 
    (calcBBInteractions 8 [(1, 3), (3, 4), (7, 7), (3, 7)]))

calcBBTests = TestList [TestLabel "Test 1" testcalcBBInteractions1, TestLabel "Test 2" testcalcBBInteractions2]

testLamPrint1 = TestCase (assertEqual "For LamApp (LamAbs 1 (LamVar 1)) (LamAbs 1 (LamVar 1)),"
    "(\\x1 -> x1) \\x1 -> x1"
    (prettyPrint (LamApp (LamAbs 1 (LamVar 1)) (LamAbs 1 (LamVar 1)))))

testLamPrint2 = TestCase (assertEqual "For LamAbs 1 (LamApp (LamVar 1) (LamAbs 1 (LamVar 1))),"
    "\\x1 -> x1 \\x1 -> x1"
    (prettyPrint (LamAbs 1 (LamApp (LamVar 1) (LamAbs 1 (LamVar 1))))))

testLamPrint3 = TestCase (assertEqual "For LamApp (LamVar 2) (LamAbs 1 (LamAbs 2 (LamVar 1))),"
    "x2 0"
    (prettyPrint (LamApp (LamVar 2) (LamAbs 1 (LamAbs 2 (LamVar 1))))))

testLamPrint4 = TestCase (assertEqual "For LamAbs 1 (LamAbs 1 (LamApp (LamVar 1) (LamAbs 1 (LamAbs 2 (LamVar 1))))),"
    "1"
    (prettyPrint (LamAbs 1 (LamAbs 1 (LamApp (LamVar 1) (LamAbs 1 (LamAbs 2 (LamVar 1))))))))

prettyPrintTest = TestList [TestLabel "Test 1" testLamPrint1, TestLabel "Test 2" testLamPrint2, TestLabel "Test 3" testLamPrint3, TestLabel "Test 4" testLamPrint4]

letTest1 = TestCase (assertEqual "For let x1 = x2"
                     Nothing 
                     (parseLet "let x1 = x2" ))

letTest2 = TestCase (assertEqual "For x1 (x2 x3)"
                     (Just (LetApp (LetVar 1) (LetApp (LetVar 2) (LetVar 3))))
                     (parseLet "x1 (x2 x3)" ))

letTest3 = TestCase (assertEqual "For x1 x2 x3"
                     (Just (LetApp (LetApp (LetVar 1) (LetVar 2)) (LetVar 3)))
                     (parseLet "x1 x2 x3" ))

letTest4 = TestCase (assertEqual "For let f1 x1 = x2 in f1 x1"
                     (Just (LetDef [([1,1], LetVar 2)] (LetApp (LetFun 1) (LetVar 1))))
                     (parseLet "let f1 x1 = x2 in f1 x1"  ))

letTest5 = TestCase (assertEqual "For let f1 x2 = x2; f2 x1 = x1 in f1 x1"
                     (Just (LetDef [([1,2],LetVar 2),([2,1],LetVar 1)] (LetApp (LetFun 1) (LetVar 1))))
                     (parseLet "let f1 x2 = x2; f2 x1 = x1 in f1 x1" ))

letParseTest = TestList [TestLabel "Test 1" letTest1, TestLabel "Test 2" letTest2, TestLabel "Test 3" letTest3, TestLabel "Test 4" letTest4, TestLabel "Test 5" letTest5]

clTest1 = TestCase (assertEqual "For \x1 → \x2 → x2"
                    (CLApp K I)
                    (clTransform (LamAbs 1 (LamAbs 2 (LamVar 2)))))

clTest2 = TestCase (assertEqual "For \x1 → \x2 → x2 x1"
                    (CLApp (CLApp S (CLApp K (CLApp S I))) (CLApp (CLApp S (CLApp K K)) I))
                    (clTransform (LamAbs 1 (LamAbs 2 (LamApp (LamVar 2) (LamVar 1))))))

clTransformTest = TestList [TestLabel "Test 1" clTest1, TestLabel "Test 2" clTest2]
