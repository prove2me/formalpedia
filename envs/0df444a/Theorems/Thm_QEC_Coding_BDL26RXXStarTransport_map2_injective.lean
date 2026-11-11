-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map2_injective
-- name    : QEC.Coding.BDL26RXXStarTransport.map2_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:18:09.712907+00:00
-- url     : https://prove2.me/theorems/7bda37b7-bd5a-42ce-82b3-405e0ac6f2ff
-- title:
--   BDL26 RXXStar Transport: map2 injective
-- statement:
--   The BDL26 RXXStar Transport construction uses the map2 injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L335-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L335-L341

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_map2_injective
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_map2_injective

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.map2_injective (h : i.val % 2=0) :
    Function.Injective ((indexedDecoderData S depth).selectedMap i).map2 := by sorry
