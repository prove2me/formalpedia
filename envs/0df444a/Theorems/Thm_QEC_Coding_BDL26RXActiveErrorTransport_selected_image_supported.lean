-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_selected_image_supported
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.selected_image_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:51:49.801626+00:00
-- url     : https://prove2.me/theorems/ff11258c-12cf-433d-871c-d97b18b9d69f
-- title:
--   BDL26 RXActive Error Transport: selected image supported
-- statement:
--   The BDL26 RXActive Error Transport construction uses the selected image supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L331-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L331-L334

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_supported

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.selected_image_supported (a b : Upper S depth i) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val) ⊆
      (NZ S depth i h a b).biUnion (zPairImage (rxData S depth i h)) := by sorry
