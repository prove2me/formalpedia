-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessTopOwner_eq
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopOwner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:29:55.106876+00:00
-- url     : https://prove2.me/theorems/9a076219-2a9f-41e3-8312-18736b227b4a
-- title:
--   BDL26 Owner Incidence Masks: witness Top Owner eq
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the witness Top Owner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L58-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L58-L59

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

theorem QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopOwner_eq (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) :
    witnessTopOwner p = Vertex.z p.1 := by sorry
