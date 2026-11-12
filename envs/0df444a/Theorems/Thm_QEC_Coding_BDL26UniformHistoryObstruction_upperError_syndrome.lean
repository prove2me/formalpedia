-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperError_syndrome
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.upperError_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:39:17.173349+00:00
-- url     : https://prove2.me/theorems/17e8b334-6d8e-4624-9df9-bfcf686aa5b6
-- title:
--   BDL26 Uniform History Obstruction: upper Error syndrome
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the upper Error syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L194-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L194-L199

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

theorem QEC.Coding.BDL26UniformHistoryObstruction.upperError_syndrome (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).coboundary1 (TopIndex (2 * j + 4))
      (upperError S j) = (upperSyndrome S j).val := by sorry
