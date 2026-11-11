-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_boundary_cocycle
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.phi_boundary_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:31:31.819952+00:00
-- url     : https://prove2.me/theorems/2ad781fb-3858-4050-9fe7-576262608d5f
-- title:
--   BDL26 RXFinite Block Transport: phi boundary cocycle
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the phi boundary cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L323-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L323-L326

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.phi_boundary_cocycle (X0 : Finset (XCoord S i)) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ
      ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b))=0 := by sorry
