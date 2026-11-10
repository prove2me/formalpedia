-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_embedded_coarse
-- name    : QEC.Coding.BDL26RXErrorPullback.embedded_coarse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:19:07.698169+00:00
-- url     : https://prove2.me/theorems/4ecd94e9-b42d-4a6b-a85d-0de2e96dfe69
-- title:
--   BDL26 RXError Pullback: embedded coarse
-- statement:
--   Canonical actual RX readout recovers every genuine embedded coarse syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback/EmbeddedReadout.lean#L113-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback/EmbeddedReadout.lean#L113-L139

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

theorem QEC.Coding.BDL26RXErrorPullback.embedded_coarse (tau : (indexedFamily S depth).Syndrome i.castSucc) :
    (rxStepOutput S depth i h (embeddedSyndrome S depth i h tau)).coarse.val = tau.val := by sorry
