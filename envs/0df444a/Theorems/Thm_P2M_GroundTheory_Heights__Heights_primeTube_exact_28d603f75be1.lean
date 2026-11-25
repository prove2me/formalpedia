-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_primeTube_exact_28d603f75be1
-- name    : P2M_GroundTheory_Heights__Heights_primeTube_exact_28d603f75be1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:41.488681+00:00
-- url     : https://prove2.me/theorems/0ce7ae30-4b40-5d78-a265-5ecb95ea1358
-- title:
--   P2 M Ground Theory Heights  Heights prime Tube exact 28d603f75be1: P2 M Ground Theory Heights  Heights prime Tube exact 28d603f75be1
-- statement:
--   The P2 M Ground Theory Heights  Heights prime Tube exact 28d603f75be1 construction uses the P2 M Ground Theory Heights  Heights prime Tube exact 28d603f75be1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeTubeVolume.lean#L40-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeTubeVolume.lean#L40-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeTubeVolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_primeTube_exact_28d603f75be1 (hL : VarietyMassLower.Statement) (hM : MassFinite.Statement) {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (thickening r (zeroSet J ∩ K)) ≤ ENNReal.ofReal (C * r ^ ((2 * n : ℤ) - 2 * d)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«primeTube_exact» := P2M_GroundTheory_Heights__Heights_primeTube_exact_28d603f75be1
