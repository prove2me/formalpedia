-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualSuffix_supports
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.actualSuffix_supports
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:33:19.839423+00:00
-- url     : https://prove2.me/theorems/6aa46313-bbc9-4d3e-b045-21a443d7eba2
-- title:
--   BDL26 Owner Incidence Masks: actual Suffix supports
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the actual Suffix supports property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/History.lean#L108-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/History.lean#L108-L111

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.actualSuffix_supports (S : OddScale) (n : Nat) (i : StepIndex n)
    (sigma : (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))).family.Syndrome i.succ) :
    ((LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)).step i sigma).componentSupports =
      (actualStep S (n + 2) (LevelTwoHistory.physicalStep i) sigma).componentSupports := by sorry
