-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_fderiv_fderiv_apply_eq_deriv_deriv_cfe20d6f28b7
-- name    : P2M_GroundTheory_Heights__Heights_FourB_fderiv_fderiv_apply_eq_deriv_deriv_cfe20d6f28b7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:42.953562+00:00
-- url     : https://prove2.me/theorems/c8dfff85-0b00-4efa-8179-37ffabd2697d
-- title:
--   P2 M Ground Theory Heights  Heights Four B fderiv fderiv apply eq deriv deriv cfe20d6f28b7: P2 M Ground Theory Heights  Heights Four B fderiv fderiv apply eq deriv deriv cfe20d6f28b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B fderiv fderiv apply eq deriv deriv cfe20d6f28b7 construction uses the P2 M Ground Theory Heights  Heights Four B fderiv fderiv apply eq deriv deriv cfe20d6f28b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviLine.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviLine.lean#L15-L33

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem P2M_GroundTheory_Heights__Heights_FourB_fderiv_fderiv_apply_eq_deriv_deriv_cfe20d6f28b7 {φ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (v : E) :
    fderiv ℝ (fderiv ℝ φ) 0 v v = deriv (deriv fun t : ℝ => φ (t • v)) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«fderiv_fderiv_apply_eq_deriv_deriv» := P2M_GroundTheory_Heights__Heights_FourB_fderiv_fderiv_apply_eq_deriv_deriv_cfe20d6f28b7
