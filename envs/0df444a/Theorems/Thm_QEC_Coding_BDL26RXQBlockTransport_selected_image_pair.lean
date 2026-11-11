-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_pair
-- name    : QEC.Coding.BDL26RXQBlockTransport.selected_image_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:25:47.502229+00:00
-- url     : https://prove2.me/theorems/8d804e00-45cf-4629-8db9-7cccfb510537
-- title:
--   BDL26 RXQBlock Transport: selected image pair
-- statement:
--   The BDL26 RXQBlock Transport construction uses the selected image pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L440-L446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L440-L446

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXQBlockTransport.selected_image_pair (q : QCoord S i) (a b : Upper S depth i)
    (z : ZCoord S i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val
      ((Data S depth i h).induced.zPairEquiv (z,copy)).val =
        (coarseSum S depth i h a b).val z := by sorry
