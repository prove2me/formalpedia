-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_supported
-- name    : QEC.Coding.BDL26RXXStarTransport.selected_image_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:06:28.641205+00:00
-- url     : https://prove2.me/theorems/dcd566c7-bfa8-4a9f-b60c-4bf30c6eda18
-- title:
--   BDL26 RXXStar Transport: selected image supported
-- statement:
--   The BDL26 RXXStar Transport construction uses the selected image supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L394-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L394-L401

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.selected_image_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a b).val) ⊆ twoCopyImage S depth i h (incidentZ S depth i x) := by sorry
