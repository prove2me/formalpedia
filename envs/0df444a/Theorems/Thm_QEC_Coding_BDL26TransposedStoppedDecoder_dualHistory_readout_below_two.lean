-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualHistory_readout_below_two
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_readout_below_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:26:00.855595+00:00
-- url     : https://prove2.me/theorems/7b623494-3aeb-4dc4-bf63-d33b40a006d4
-- title:
--   BDL26 Transposed Stopped Decoder: dual History readout below two
-- statement:
--   The BDL26 Transposed Stopped Decoder construction uses the dual History readout below two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L62-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder.lean#L62-L66

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualHistory_readout_below_two (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (i : LevelIndex (n + 2)) (hi : i.val < 2) :
    LevelTwoHistory.syndromeReadout (dualDecoderData S (n + 2)) (dualHistory S n sigma) i = 0 := by sorry
