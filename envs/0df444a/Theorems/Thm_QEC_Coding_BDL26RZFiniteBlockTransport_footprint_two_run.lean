-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_footprint_two_run
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.footprint_two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:16:46.23343+00:00
-- url     : https://prove2.me/theorems/202158c4-8ce6-43fd-8ffe-c37d98259bd6
-- title:
--   BDL26 RZFinite Block Transport: footprint two run
-- statement:
--   No caller cover: the original physical error support supplies the finite footprint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L900-L903
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L900-L903

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.footprint_two_run (above : 2 ≤ i.val) (a b : Upper S depth i) :
    ∃ p : Potential S depth i, Pullback S depth i odd
      (footprintQ S depth i odd a b) (footprintZ S depth i odd a b) a b p := by sorry
