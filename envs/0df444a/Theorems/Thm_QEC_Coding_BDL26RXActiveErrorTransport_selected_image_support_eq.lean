-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_selected_image_support_eq
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.selected_image_support_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:48:35.457912+00:00
-- url     : https://prove2.me/theorems/478d0eea-d0f6-41b6-936d-1292a22e8a13
-- title:
--   BDL26 RXActive Error Transport: selected image support eq
-- statement:
--   The BDL26 RXActive Error Transport construction uses the selected image support eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L326-L329
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L326-L329

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_support_eq
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_support_eq
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_support_eq

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.selected_image_support_eq (a b : Upper S depth i) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val) =
      (hammingSupport (coarseSum S depth i h a b).val).biUnion (zPairImage (rxData S depth i h)) := by sorry
