-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_selected_image_pair
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.selected_image_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:08:40.292961+00:00
-- url     : https://prove2.me/theorems/e6ae665a-d464-4440-b5ef-fa174d59d1d4
-- title:
--   BDL26 RXPhysical Star Transport: selected image pair
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the selected image pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L314-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L314-L317

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_pair
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_pair
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_pair

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXPhysicalStarTransport.selected_image_pair (a b : Upper S depth i) (z : ZCoord S i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val
      ((rxData S depth i h).induced.zPairEquiv (z,copy)).val=(coarseSum S depth i h a b).val z := by sorry
