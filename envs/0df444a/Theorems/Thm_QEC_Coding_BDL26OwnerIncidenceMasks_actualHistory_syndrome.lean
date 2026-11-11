-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualHistory_syndrome
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.actualHistory_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:00:54.599119+00:00
-- url     : https://prove2.me/theorems/846b290c-27af-4e96-b8e1-a85f0ce7e138
-- title:
--   BDL26 Owner Incidence Masks: actual History syndrome
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the actual History syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/History.lean#L87-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/History.lean#L87-L93

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.actualHistory_syndrome (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    (indexedFamily S (n + 2)).coboundary1 (TopIndex (n + 2))
      (historyLiftedCorrection (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2)))
        (actualHistory S n sigma)) = sigma.val := by sorry
