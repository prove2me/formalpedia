-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessNextOutput_input
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.witnessNextOutput_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:30:38.598166+00:00
-- url     : https://prove2.me/theorems/e156f0de-a08c-42bf-a313-26fdae284870
-- title:
--   BDL26 Owner Incidence Masks: witness Next Output input
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the witness Next Output input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L180-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L180-L182

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

theorem QEC.Coding.BDL26OwnerIncidenceMasks.witnessNextOutput_input : witnessNextOutput.input = witnessLower := by sorry
