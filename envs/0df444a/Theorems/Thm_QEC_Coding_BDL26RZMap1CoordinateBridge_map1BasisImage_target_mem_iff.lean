-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map1BasisImage_target_mem_iff
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.map1BasisImage_target_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:18:07.329201+00:00
-- url     : https://prove2.me/theorems/83983db2-99c8-4bc9-ba6f-e5d075c0cd01
-- title:
--   BDL26 RZMap1 Coordinate Bridge: map1 Basis Image target mem iff
-- statement:
--   Exact F11 image characterization, stated in both directions rather than
--   as a one-way support bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L948-L953
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L948-L953

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZMap1CoordinateBridge
open scoped BigOperators
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
open BDL26RZLocalReplacement
open MultiscaleDecoder
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.rzQDecidableEq
attribute [local instance] rzQFintype
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.subdivisionEdgeDecidableEq
attribute [local instance] subdivisionEdgeDecidableEq
universe u

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.map1BasisImage_target_mem_iff
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) (target : RZQ P S) :
    target ∈ rzMap1ParentRegion P A4 S q ↔
      map1BasisImage P A4 S q target ≠ 0 := by sorry
