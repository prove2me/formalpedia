-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessHistory_prefix
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.witnessHistory_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:34:15.530419+00:00
-- url     : https://prove2.me/theorems/fab97071-485e-4e13-994e-f886eb66fe1e
-- title:
--   BDL26 Owner Incidence Masks: witness History prefix
-- statement:
--   The tested outputs are literally the first two entries of the actual stopped history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L160-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L160-L166

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

theorem QEC.Coding.BDL26OwnerIncidenceMasks.witnessHistory_prefix : ∃ tail,
    actualHistory scaleFive 2 witnessUpper =
      CorrectionHistoryEntry.step (1 : StepIndex 2)
        (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 1 witnessTopOutput) ::
      CorrectionHistoryEntry.step (0 : StepIndex 2)
        (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 0 witnessNextOutput) :: tail := by sorry
