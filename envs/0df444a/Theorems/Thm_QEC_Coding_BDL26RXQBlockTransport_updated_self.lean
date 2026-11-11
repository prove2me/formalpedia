-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_updated_self
-- name    : QEC.Coding.BDL26RXQBlockTransport.updated_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:33:04.300223+00:00
-- url     : https://prove2.me/theorems/0ed3c0f1-4d72-45ed-8862-cb02d4b7314d
-- title:
--   BDL26 RXQBlock Transport: updated self
-- statement:
--   The BDL26 RXQBlock Transport construction uses the updated self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L499-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L499-L501

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXQBlockTransport.updated_self (a : Upper S depth i) : updated S depth i h a a=0 := by sorry
