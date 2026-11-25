-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_fderiv_half_log_apply_b1700aa98f9b
-- name    : P2M_GroundTheory_Heights__Heights_ChartGram_fderiv_half_log_apply_b1700aa98f9b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:56.548092+00:00
-- url     : https://prove2.me/theorems/1b587a96-8259-4c36-8834-ec4883705e15
-- title:
--   P2 M Ground Theory Heights  Heights Chart Gram fderiv half log apply b1700aa98f9b: P2 M Ground Theory Heights  Heights Chart Gram fderiv half log apply b1700aa98f9b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Gram fderiv half log apply b1700aa98f9b construction uses the P2 M Ground Theory Heights  Heights Chart Gram fderiv half log apply b1700aa98f9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L29-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped InnerProductSpace
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem P2M_GroundTheory_Heights__Heights_ChartGram_fderiv_half_log_apply_b1700aa98f9b {u : E → F} {y : E}
    (hu : DifferentiableAt ℂ u y) (h0 : u y ≠ 0) (b : E) :
    fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y b =
      (⟪u y, fderiv ℂ u y b⟫_ℂ).re * ((⟪u y, u y⟫_ℂ).re)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartGram».«fderiv_half_log_apply» := P2M_GroundTheory_Heights__Heights_ChartGram_fderiv_half_log_apply_b1700aa98f9b
