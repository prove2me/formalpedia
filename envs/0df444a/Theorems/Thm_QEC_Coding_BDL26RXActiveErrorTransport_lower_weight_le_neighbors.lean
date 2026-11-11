-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_lower_weight_le_neighbors
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.lower_weight_le_neighbors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:23:28.583183+00:00
-- url     : https://prove2.me/theorems/c146aad9-26d9-44b2-8289-f05ba23c1757
-- title:
--   BDL26 RXActive Error Transport: lower weight le neighbors
-- statement:
--   The BDL26 RXActive Error Transport construction uses the lower weight le neighbors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L346-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L346-L348

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.lower_weight_le_neighbors (a b : Upper S depth i) :
    HammingWeight (L S depth i h a b) ≤ (N S depth i h a b).card := by sorry
