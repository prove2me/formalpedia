-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_supported
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.phi_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:08:25.851223+00:00
-- url     : https://prove2.me/theorems/03fff854-ebe2-496e-b843-b50701845e11
-- title:
--   BDL26 RXFinite Block Transport: phi supported
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the phi supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L296-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L296-L304

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.phi_supported (X0 : Finset (XCoord S i)) (a b : Upper S depth i) :
    hammingSupport (Phi S depth i h X0 a b) ⊆ degreeZeroBlocks S depth i h X0 := by sorry
