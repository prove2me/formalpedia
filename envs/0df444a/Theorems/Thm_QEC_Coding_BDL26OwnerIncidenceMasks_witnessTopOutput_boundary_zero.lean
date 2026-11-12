-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessTopOutput_boundary_zero
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopOutput_boundary_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:34:41.489294+00:00
-- url     : https://prove2.me/theorems/ebe66abd-01c8-406a-adc2-83493d89ad38
-- title:
--   BDL26 Owner Incidence Masks: witness Top Output boundary zero
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the witness Top Output boundary zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L170-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L170-L174

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

theorem QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopOutput_boundary_zero
    (j : Fin witnessTopOutput.localComponents.length) :
    witnessTopOutput.componentCoboundaryAt j = 0 := by sorry
