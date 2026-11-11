-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndrome_weight_le_four
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndrome_weight_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:32:42.736101+00:00
-- url     : https://prove2.me/theorems/5c851e2f-6d0b-46dd-8242-a66e674dda9e
-- title:
--   BDL26 Uniform History Obstruction: lower Syndrome weight le four
-- statement:
--   Measured all-state valence bounds the actual lower syndrome uniformly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L43-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L43-L46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndrome_weight_le_four (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val ≤ 4 := by sorry
