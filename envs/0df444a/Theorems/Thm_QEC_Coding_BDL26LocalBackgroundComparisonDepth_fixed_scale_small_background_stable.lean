-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_fixed_scale_small_background_stable
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonDepth.fixed_scale_small_background_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:28:16.633843+00:00
-- url     : https://prove2.me/theorems/1b1463ec-7385-4109-aebc-3410ee98b05f
-- title:
--   BDL26 Local Background Comparison Depth: fixed scale small background stable
-- statement:
--   Stability at a fixed scale, with the budget controlled by depth rather than scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L78-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L78-L84

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonDepth.fixed_scale_small_background_stable (S : OddScale) (n B : Nat)
    (large : 33 ≤ S.ell) (deep : 4*B < 2 ^ ((n+1)/2))
    (g : W S n) (small : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.SingleFlipStable S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g) := by sorry
