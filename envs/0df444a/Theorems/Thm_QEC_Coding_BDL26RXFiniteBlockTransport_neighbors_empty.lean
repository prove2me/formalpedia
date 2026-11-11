-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_neighbors_empty
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.neighbors_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:01:34.362534+00:00
-- url     : https://prove2.me/theorems/6d50be1e-47ec-4909-be82-94e0114d9f68
-- title:
--   BDL26 RXFinite Block Transport: neighbors empty
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the neighbors empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L562-L563
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L562-L563

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.neighbors_empty (Q0 : Finset (QCoord S i)) : neighbors S depth i ∅ Q0=Q0 := by sorry
