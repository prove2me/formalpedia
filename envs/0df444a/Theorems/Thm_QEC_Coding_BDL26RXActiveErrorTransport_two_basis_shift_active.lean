-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_two_basis_shift_active
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.two_basis_shift_active
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:15:40.979877+00:00
-- url     : https://prove2.me/theorems/20735ca5-eeeb-4ce4-afa9-d7af18ce3c31
-- title:
--   BDL26 RXActive Error Transport: two basis shift active
-- statement:
--   Exact Q-only active labels for two distinct actual lower basis labels and any original background.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L541-L567
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L541-L567

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.two_basis_shift_active (q0 q1 : QCoord S i) (hn : q0≠q1) (a : Upper S depth i) :
    let w : Lower S depth i := canonicalBasisWord q0+canonicalBasisWord q1
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 w
    activeX S depth i h (a+b)=∅ ∧ activeQ S depth i h (a+b)={q0,q1} := by sorry
