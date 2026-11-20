-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_zero_seed_c2_weight
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonDepth.zero_seed_c2_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:28:34.823157+00:00
-- url     : https://prove2.me/theorems/d179adfc-2688-4953-a897-bb8121b39ef9
-- title:
--   BDL26 Local Background Comparison Depth: zero seed c2 weight
-- statement:
--   The actual full global C2 readout obeys the global alternating contraction.
--   No marked-component restriction theorem is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L44-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L44-L59

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonDepth.zero_seed_c2_weight (S : OddScale) (n : Nat) (g : W S n) :
    2 ^ ((n+1)/2) * HammingWeight
      (BDL26AllDepthBottomComparisonStability.baseReadout S n
        (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)) ≤
      4 * HammingWeight g := by sorry
