-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_coarse_apply
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.coarse_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:26:23.139348+00:00
-- url     : https://prove2.me/theorems/c977c71e-2012-4ed4-be67-1c7185d0a8f0
-- title:
--   BDL26 RXFinite Block Transport: coarse apply
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the coarse apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L482-L493
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L482-L493

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.coarse_apply (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      ∑ q ∈ neighbors S depth i X0 Q0, L S depth i h X0 a b q *
        (if (state S i.val).presentation.qz q z=true then 1 else 0) := by sorry
