-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_singleton
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.phi_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:59:58.096203+00:00
-- url     : https://prove2.me/theorems/fe42eba9-a2b7-4ea9-8730-b9a3771cc8db
-- title:
--   BDL26 RXFinite Block Transport: phi singleton
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the phi singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L573-L574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L573-L574

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.phi_singleton (x : XCoord S i) (a b : Upper S depth i) :
    Phi S depth i h {x} a b=BDL26RXXStarTransport.potential S depth i h x a b := by sorry
