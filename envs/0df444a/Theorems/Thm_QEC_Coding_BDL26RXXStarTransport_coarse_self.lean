-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_self
-- name    : QEC.Coding.BDL26RXXStarTransport.coarse_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:57:34.64429+00:00
-- url     : https://prove2.me/theorems/1203a2e6-92f2-40d2-a421-b0cf46a116cb
-- title:
--   BDL26 RXXStar Transport: coarse self
-- statement:
--   The BDL26 RXXStar Transport construction uses the coarse self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L439-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L439-L439

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_coarse_self

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.coarse_self (a : Upper S depth i) : (coarseSum S depth i h a a).val=0 := by sorry
