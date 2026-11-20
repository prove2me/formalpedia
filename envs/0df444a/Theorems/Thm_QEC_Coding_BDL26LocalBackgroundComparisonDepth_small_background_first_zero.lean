-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_small_background_first_zero
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonDepth.small_background_first_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:31:44.726054+00:00
-- url     : https://prove2.me/theorems/8e96ee5b-0e19-42d1-a3c7-a2011de8b650
-- title:
--   BDL26 Local Background Comparison Depth: small background first zero
-- statement:
--   A bounded physical background at sufficient depth has literally zero FIRST.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L62-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L62-L75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalBackgroundComparisonDepth.small_background_first_zero (S : OddScale) (n B : Nat)
    (deep : 4*B < 2 ^ ((n+1)/2)) (g : W S n)
    (small : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.baseReadout S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)=0 := by sorry
