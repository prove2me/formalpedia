-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_embedded_correction_eq_zero_input
-- name    : QEC.Coding.BDL26RXErrorPullback.embedded_correction_eq_zero_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:18:54.379253+00:00
-- url     : https://prove2.me/theorems/e33b446e-f40d-4e7d-be67-214ae68d85d3
-- title:
--   BDL26 RXError Pullback: embedded correction eq zero input
-- statement:
--   The literal map2 lift does not change the chosen correction from the zero run.
--   This states equality of actual selectors, not additivity of a decoder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback/EmbeddedReadout.lean#L85-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback/EmbeddedReadout.lean#L85-L95

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXErrorPullback.embedded_correction_eq_zero_input
    (s : (indexedFamily S depth).Cochain2 i.castSucc) :
    rxCorrectionTotal (Data S depth i h) (((indexedDecoderData S depth).rxMap i).map2 s) =
      rxCorrectionTotal (Data S depth i h) 0 := by sorry
