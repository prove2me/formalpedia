-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualHistory_readout_below_two
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.actualHistory_readout_below_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:17:19.134117+00:00
-- url     : https://prove2.me/theorems/cff4e1a1-315b-4b6f-8aab-95040efdb370
-- title:
--   BDL26 Owner Incidence Masks: actual History readout below two
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the actual History readout below two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/History.lean#L95-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/History.lean#L95-L100

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.actualHistory_readout_below_two (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (i : LevelIndex (n + 2)) (hi : i.val < 2) :
    LevelTwoHistory.syndromeReadout (indexedDecoderData S (n + 2))
      (actualHistory S n sigma) i = 0 := by sorry
