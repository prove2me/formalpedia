-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_levi_eq_deriv_deriv_1a5664901ce5
-- name    : P2M_GroundTheory_Heights__Heights_FourB_levi_eq_deriv_deriv_1a5664901ce5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:24.875524+00:00
-- url     : https://prove2.me/theorems/31c5d6ed-3fc0-5360-8a88-a23068d17ae2
-- title:
--   P2 M Ground Theory Heights  Heights Four B levi eq deriv deriv 1a5664901ce5: P2 M Ground Theory Heights  Heights Four B levi eq deriv deriv 1a5664901ce5
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B levi eq deriv deriv 1a5664901ce5 construction uses the P2 M Ground Theory Heights  Heights Four B levi eq deriv deriv 1a5664901ce5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviLine.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviLine.lean#L59-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm Filter Topology Polynomial
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FourB_levi_eq_deriv_deriv_1a5664901ce5 {φ : (ι → ℂ) → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (w : ι → ℂ) :
    levi φ 0 w = (deriv (deriv fun t : ℝ => φ (t • w)) 0 +
      deriv (deriv fun t : ℝ => φ (t • (Complex.I • w))) 0) / 4 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«levi_eq_deriv_deriv» := P2M_GroundTheory_Heights__Heights_FourB_levi_eq_deriv_deriv_1a5664901ce5
