-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessHistory_exact
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.witnessHistory_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:30:38.710333+00:00
-- url     : https://prove2.me/theorems/29f18df3-36cc-4f51-9205-bc23dfceea69
-- title:
--   BDL26 Owner Incidence Masks: witness History exact
-- statement:
--   All three entries, including the executable physical-C2 correction, are
--   exactly the real history producing the top and next outputs above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L144-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L144-L157

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

theorem QEC.Coding.BDL26OwnerIncidenceMasks.witnessHistory_exact : actualHistory scaleFive 2 witnessUpper =
    [CorrectionHistoryEntry.step (1 : StepIndex 2)
      (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 1 witnessTopOutput),
     CorrectionHistoryEntry.step (0 : StepIndex 2)
      (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 0 witnessNextOutput),
     CorrectionHistoryEntry.base witnessBaseEntry] := by sorry
