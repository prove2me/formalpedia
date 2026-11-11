-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessNextOwner_eq
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.witnessNextOwner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:30:15.752812+00:00
-- url     : https://prove2.me/theorems/8e8a3b86-609f-4e2f-b04c-4010bc303d37
-- title:
--   BDL26 Owner Incidence Masks: witness Next Owner eq
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the witness Next Owner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L176-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L176-L178

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.witnessNextOwner_eq (p : FamilyZ scaleFive 4 (3 : LevelIndex 4)) :
    witnessNextOwner p = rxSyndromeOwner evidenceStateTwo.presentation scaleFive p := by sorry
