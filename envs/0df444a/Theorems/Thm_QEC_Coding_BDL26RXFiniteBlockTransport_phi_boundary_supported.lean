-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_boundary_supported
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.phi_boundary_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:18:51.829277+00:00
-- url     : https://prove2.me/theorems/d73aea11-391c-4934-bb5d-84de78b57874
-- title:
--   BDL26 RXFinite Block Transport: phi boundary supported
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the phi boundary supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L306-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L306-L321

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.phi_boundary_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) :
    hammingSupport ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b)) ⊆
      star S depth i h X0 Q0 := by sorry
