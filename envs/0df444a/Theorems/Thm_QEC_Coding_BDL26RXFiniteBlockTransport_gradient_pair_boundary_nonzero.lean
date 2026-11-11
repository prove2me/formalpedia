-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_boundary_nonzero
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_boundary_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:05:03.125909+00:00
-- url     : https://prove2.me/theorems/6983878d-cbfa-4c20-9605-da45b500cd7e
-- title:
--   BDL26 RXFinite Block Transport: gradient pair boundary nonzero
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the gradient pair boundary nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L681-L690
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L681-L690

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_boundary_nonzero (x0 x1 : XCoord S i) (hne : x0≠x1)
    (a : Upper S depth i) :
    (indexedFamily S depth).coboundary0 i.succ
      (Phi S depth i h {x0,x1} a
        (a+(gradientError S depth i h x0+gradientError S depth i h x1))) ≠ 0 := by sorry
