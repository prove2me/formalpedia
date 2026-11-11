-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self
-- name    : QEC.Coding.BDL26RXXStarTransport.word_add_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:19:22.716202+00:00
-- url     : https://prove2.me/theorems/b79a452b-1ae2-4e95-a804-9c51fc8c2654
-- title:
--   BDL26 RXXStar Transport: word add self
-- statement:
--   The BDL26 RXXStar Transport construction uses the word add self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L57-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L57-L59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.word_add_self {ι : Type*} (w : Word BDL26Field ι) : w+w=0 := by sorry
