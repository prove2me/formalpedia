-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_old_x_star
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.old_x_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:15:50.326853+00:00
-- url     : https://prove2.me/theorems/c00bc840-e33d-418e-a714-f282a6746f39
-- title:
--   BDL26 RZFinite Block Transport: old x star
-- statement:
--   The stated OLD X-star input union; no upper-star-to-parent identification is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L953-L958
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L953-L958

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)

theorem QEC.Coding.BDL26RZFiniteBlockTransport.old_x_star (above : 2 ≤ i.val) (x : (Old S depth i).X) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ inputBlocks S depth i odd
      (incidentQ S depth i x) (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x))) :
    ∃ p : Potential S depth i, Pullback S depth i odd
      (incidentQ S depth i x) (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x)) a b p := by sorry
