-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_exterior
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.selected_image_exterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:12:04.4362+00:00
-- url     : https://prove2.me/theorems/90a7c16e-5ff2-4a25-b22e-5f336d7878c9
-- title:
--   BDL26 RXFinite Block Transport: selected image exterior
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the selected image exterior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L529-L532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L529-L532

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_exterior
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_exterior

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.selected_image_exterior (a b : Upper S depth i) (p : FamilyZ S depth i.succ)
    (hp : p ∉ (rxData S depth i h).zSector) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val p=0 := by sorry
