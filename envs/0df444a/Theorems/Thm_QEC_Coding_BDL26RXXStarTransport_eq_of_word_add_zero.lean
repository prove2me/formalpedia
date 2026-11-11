-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_eq_of_word_add_zero
-- name    : QEC.Coding.BDL26RXXStarTransport.eq_of_word_add_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:35:33.203203+00:00
-- url     : https://prove2.me/theorems/29017c0d-6f38-4823-9ec0-7b99fe2649ad
-- title:
--   BDL26 RXXStar Transport: eq of word add zero
-- statement:
--   The BDL26 RXXStar Transport construction uses the eq of word add zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L61-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L61-L65

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

theorem QEC.Coding.BDL26RXXStarTransport.eq_of_word_add_zero {ι : Type*} (u v : Word BDL26Field ι)
    (hh : u+v=0) : u=v := by sorry
