-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_potential_oldX_zero
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.potential_oldX_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:34:40.791631+00:00
-- url     : https://prove2.me/theorems/27fd6573-abed-4890-8690-870629100884
-- title:
--   BDL26 RZFinite Block Transport: potential old X zero
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the potential old X zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L975-L982
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L975-L982

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.potential_oldX_zero (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (p : Potential S depth i)
    (hp : hammingSupport p ⊆ potentialStar S depth i odd Q0 Z0)
    (x : (Old S depth i).X) (copy : BDL26FiniteTannerSquare.Two) :
    read0 S depth i odd p (.inr (x,copy))=0 := by sorry
