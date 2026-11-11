-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_seedWord_nonzero
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.seedWord_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:19:00.724208+00:00
-- url     : https://prove2.me/theorems/0c31d467-cc88-42c2-a056-dcfe3dcf5625
-- title:
--   BDL26 RXFinite Block Transport: seed Word nonzero
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the seed Word nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L772-L775
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L772-L775

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
open BDL26FiniteAlternatingCore

theorem QEC.Coding.BDL26RXFiniteBlockTransport.seedWord_nonzero : seedWord≠0 := by sorry
