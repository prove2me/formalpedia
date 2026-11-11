-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndrome_weight_eq
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndrome_weight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:32:56.391463+00:00
-- url     : https://prove2.me/theorems/d4a81d5b-83ef-43f0-8361-868178dc9c52
-- title:
--   BDL26 Uniform History Obstruction: lower Syndrome weight eq
-- statement:
--   The actual lower syndrome counts the successor state's measured degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L34-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L34-L40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndrome_weight_eq (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val =
      qZDegree (state S (2 * j + 3)).presentation (lowerBasis S j) := by sorry
