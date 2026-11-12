-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessUpperError_syndrome
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.witnessUpperError_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:37:28.266866+00:00
-- url     : https://prove2.me/theorems/1c6e7b5e-c354-43d7-a67e-ad497c9bf0ff
-- title:
--   BDL26 Owner Incidence Masks: witness Upper Error syndrome
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the witness Upper Error syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L204-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L204-L208

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

theorem QEC.Coding.BDL26OwnerIncidenceMasks.witnessUpperError_syndrome :
    (indexedFamily scaleFive 4).coboundary1 (4 : LevelIndex 4) witnessUpperError = witnessUpper.val := by sorry
