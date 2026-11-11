-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_support_of_zero_off
-- name    : QEC.Coding.BDL26RXXStarTransport.support_of_zero_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:21:43.119188+00:00
-- url     : https://prove2.me/theorems/6f0b249a-35d5-4a0e-90a6-555374d04f7a
-- title:
--   BDL26 RXXStar Transport: support of zero off
-- statement:
--   The BDL26 RXXStar Transport construction uses the support of zero off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L73-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L73-L78

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

theorem QEC.Coding.BDL26RXXStarTransport.support_of_zero_off {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Word BDL26Field ι) (Y : Finset ι)
    (hw : ∀ p, p ∉ Y → w p=0) : hammingSupport w ⊆ Y := by sorry
