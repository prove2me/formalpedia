-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_cylinderVertexMatrixExecutable_eq
-- name    : QEC.Coding.BDL26LevelTwoDecoder.cylinderVertexMatrixExecutable_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:49:24.436198+00:00
-- url     : https://prove2.me/theorems/71be4602-8a89-42ba-b3f6-eb689d7749a0
-- title:
--   BDL26 Level Two Decoder: cylinder Vertex Matrix Executable eq
-- statement:
--   The BDL26 Level Two Decoder construction uses the cylinder Vertex Matrix Executable eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoder.lean#L413-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoder.lean#L413-L418

import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Encodable.Basic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26RXLocalReplacement BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.presentationXDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.presentationQDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.presentationZDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.presentationFaceDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.edgeDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.xStarVertexDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.xStarEdgeDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.xStarFaceDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.subdivisionVertexDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.subdivisionEdgeDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.subdivisionFaceDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.subdivisionBoundaryVertexDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.subdivisionBoundaryEdgeDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.doubleCylinderVertexDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.doubleCylinderEdgeDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.doubleCylinderFaceDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.qStarEdgeDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.qStarVertexDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.qSubdivisionVertexDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.qSubdivisionEdgeDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.qDoubleCylinderVertexDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.qDoubleCylinderEdgeDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.rx0DecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.rx1DecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.rx2DecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.rxLocalFaceDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.rxGlueFaceDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.rxFaceDecEq

theorem QEC.Coding.BDL26LevelTwoDecoder.cylinderVertexMatrixExecutable_eq (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) :
    cylinderVertexMatrixExecutable P x S = doubleCylinderEdgeVertexMatrix P x S := by sorry
