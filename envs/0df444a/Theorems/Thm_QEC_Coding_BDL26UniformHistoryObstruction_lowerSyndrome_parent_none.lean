-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndrome_parent_none
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndrome_parent_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:31:39.957227+00:00
-- url     : https://prove2.me/theorems/c2563d08-9f5f-449c-9015-2dac4ef0c4a7
-- title:
--   BDL26 Uniform History Obstruction: lower Syndrome parent none
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the lower Syndrome parent none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L236-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L236-L259

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndrome_parent_none (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 3)).presentation.Z)
    (hz : (lowerSyndrome S j).val z ≠ 0) :
    parent S (2 * j + 3) (.z z) = none := by sorry
