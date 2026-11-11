-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_boundary_other_x
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.phi_boundary_other_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:31:29.641499+00:00
-- url     : https://prove2.me/theorems/b577b099-8c4f-4938-a234-f878ce2991b2
-- title:
--   BDL26 RXFinite Block Transport: phi boundary other x
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the phi boundary other x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L339-L346
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L339-L346

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.phi_boundary_other_x (X0 : Finset (XCoord S i)) (x : XCoord S i) (hx : x ∉ X0)
    (a b : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b))=0 := by sorry
