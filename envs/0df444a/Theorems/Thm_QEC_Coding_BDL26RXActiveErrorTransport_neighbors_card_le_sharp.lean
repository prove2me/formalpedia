-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_neighbors_card_le_sharp
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.neighbors_card_le_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:24:43.65676+00:00
-- url     : https://prove2.me/theorems/98d15a7b-e4ff-45cb-bf1d-da1ed00a4ecf
-- title:
--   BDL26 RXActive Error Transport: neighbors card le sharp
-- statement:
--   The BDL26 RXActive Error Transport construction uses the neighbors card le sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L350-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L350-L353

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.neighbors_card_le_sharp (a b : Upper S depth i) :
    (N S depth i h a b).card ≤ (activeQ S depth i h (a+b)).card +
      ∑ x ∈ activeX S depth i h (a+b), (incidentQ S depth i x).card := by sorry
