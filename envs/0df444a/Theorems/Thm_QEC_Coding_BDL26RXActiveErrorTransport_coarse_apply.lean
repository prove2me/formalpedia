-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_coarse_apply
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.coarse_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:49:59.8152+00:00
-- url     : https://prove2.me/theorems/36cb2142-0485-49c5-aced-e2f451db6003
-- title:
--   BDL26 RXActive Error Transport: coarse apply
-- statement:
--   The BDL26 RXActive Error Transport construction uses the coarse apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L318-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L318-L321

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_coarse_apply
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXActiveErrorTransport.coarse_apply (a b : Upper S depth i) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z = ∑ q ∈ N S depth i h a b, L S depth i h a b q *
      (if (state S i.val).presentation.qz q z=true then 1 else 0) := by sorry
