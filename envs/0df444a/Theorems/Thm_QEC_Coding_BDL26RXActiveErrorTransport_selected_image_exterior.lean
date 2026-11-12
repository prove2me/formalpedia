-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_selected_image_exterior
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.selected_image_exterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:51:47.702547+00:00
-- url     : https://prove2.me/theorems/d9e64ec1-1890-485f-ad55-73b4b949366f
-- title:
--   BDL26 RXActive Error Transport: selected image exterior
-- statement:
--   The BDL26 RXActive Error Transport construction uses the selected image exterior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L341-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L341-L344

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_exterior
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_exterior
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_exterior

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.selected_image_exterior (a b : Upper S depth i) (p : FamilyZ S depth i.succ)
    (hp : p ∉ (rxData S depth i h).zSector) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val p=0 := by sorry
