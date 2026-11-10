-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_mem_wordsOn
-- name    : QEC.Coding.BDL26LevelTwoDecoder.mem_wordsOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:44:52.949977+00:00
-- url     : https://prove2.me/theorems/2aeacbc0-5354-406e-bc7c-0bd829afa325
-- title:
--   BDL26 Level Two Decoder: mem words On
-- statement:
--   Every binary word vanishing off the coordinate list is enumerated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoder.lean#L500-L523
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoder.lean#L500-L523

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
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.zCylinderVertexDecEq
attribute [local instance] QEC.Coding.BDL26LevelTwoDecoder.rzQExecutableFintype

theorem QEC.Coding.BDL26LevelTwoDecoder.mem_wordsOn {α : Type} [DecidableEq α] (qs : List α)
    (e : Word (ZMod 2) α) (houtside : ∀ q, q ∉ qs → e q = 0) :
    e ∈ wordsOn qs := by sorry
