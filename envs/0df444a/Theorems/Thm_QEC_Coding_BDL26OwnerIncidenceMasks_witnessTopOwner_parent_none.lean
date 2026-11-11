-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessTopOwner_parent_none
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopOwner_parent_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:29:15.843892+00:00
-- url     : https://prove2.me/theorems/9ee41844-e224-44c0-800e-df83f2cd5bc0
-- title:
--   BDL26 Owner Incidence Masks: witness Top Owner parent none
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the witness Top Owner parent none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L61-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L61-L65

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

theorem QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopOwner_parent_none (p : FamilyZ scaleFive 4 (4 : LevelIndex 4))
    (hp : witnessUpper.val p ≠ 0) : parent scaleFive 3 (witnessTopOwner p) = none := by sorry
