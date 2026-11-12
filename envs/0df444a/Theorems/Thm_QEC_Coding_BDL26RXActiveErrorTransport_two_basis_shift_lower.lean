-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_two_basis_shift_lower
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.two_basis_shift_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:51:37.093681+00:00
-- url     : https://prove2.me/theorems/a94a2997-7dd9-4284-b734-29c40353da22
-- title:
--   BDL26 RXActive Error Transport: two basis shift lower
-- statement:
--   The BDL26 RXActive Error Transport construction uses the two basis shift lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L569-L575
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L569-L575

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
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

theorem QEC.Coding.BDL26RXActiveErrorTransport.two_basis_shift_lower (q0 q1 : QCoord S i) (hn : q0≠q1) (a : Upper S depth i) :
    let w : Lower S depth i := canonicalBasisWord q0+canonicalBasisWord q1
    L S depth i h a (a+((indexedDecoderData S depth).selectedMap i).map1 w)=w := by sorry
