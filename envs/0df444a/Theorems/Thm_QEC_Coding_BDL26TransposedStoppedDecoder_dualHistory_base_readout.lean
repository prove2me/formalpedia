-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualHistory_base_readout
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_base_readout
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:22:49.760426+00:00
-- url     : https://prove2.me/theorems/21518f45-c92e-4853-9037-94fa0f6475dd
-- title:
--   BDL26 Transposed Stopped Decoder: dual History base readout
-- statement:
--   The BDL26 Transposed Stopped Decoder construction uses the dual History base readout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L68-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L68-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_base_readout (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    LevelTwoHistory.syndromeReadout (dualDecoderData S (n + 2)) (dualHistory S n sigma)
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n)) =
      (terminalInput (LevelTwoHistory.suffixData (dualDecoderData S (n + 2)))
        (LevelTwoHistory.suffixSteps _ (dualAboveTwoSteps S n)) sigma).val := by sorry
