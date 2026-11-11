-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_two_basis_shift_weight_le_two
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.two_basis_shift_weight_le_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:52:54.078028+00:00
-- url     : https://prove2.me/theorems/ff48dc61-8c74-4d82-bcb0-56ac77adab60
-- title:
--   BDL26 RXActive Error Transport: two basis shift weight le two
-- statement:
--   The BDL26 RXActive Error Transport construction uses the two basis shift weight le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L577-L585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L577-L585

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.two_basis_shift_weight_le_two (q0 q1 : QCoord S i) (hn : q0≠q1) (a : Upper S depth i) :
    let w : Lower S depth i := canonicalBasisWord q0+canonicalBasisWord q1
    HammingWeight (L S depth i h a (a+((indexedDecoderData S depth).selectedMap i).map1 w)) ≤ 2 := by sorry
