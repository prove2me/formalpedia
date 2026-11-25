-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_hessian_half_log_apply_0b4ec8f4ab65
-- name    : P2M_GroundTheory_Heights__Heights_ChartGram_hessian_half_log_apply_0b4ec8f4ab65
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:22.001385+00:00
-- url     : https://prove2.me/theorems/169b5486-be63-4789-aee2-701d11f0b6bf
-- title:
--   P2 M Ground Theory Heights  Heights Chart Gram hessian half log apply 0b4ec8f4ab65: P2 M Ground Theory Heights  Heights Chart Gram hessian half log apply 0b4ec8f4ab65
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Gram hessian half log apply 0b4ec8f4ab65 construction uses the P2 M Ground Theory Heights  Heights Chart Gram hessian half log apply 0b4ec8f4ab65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L43-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L43-L86

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

theorem P2M_GroundTheory_Heights__Heights_ChartGram_hessian_half_log_apply_0b4ec8f4ab65 [CompleteSpace F] {u : E → F} {y : E}
    (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re)) y a b =
      ((⟪u y, fderiv ℂ (fderiv ℂ u) y a b⟫_ℂ).re + (⟪fderiv ℂ u y a, fderiv ℂ u y b⟫_ℂ).re) *
          ((⟪u y, u y⟫_ℂ).re)⁻¹ -
        (⟪u y, fderiv ℂ u y b⟫_ℂ).re * (2 * (⟪u y, fderiv ℂ u y a⟫_ℂ).re) *
          (((⟪u y, u y⟫_ℂ).re) ^ 2)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartGram».«hessian_half_log_apply» := P2M_GroundTheory_Heights__Heights_ChartGram_hessian_half_log_apply_0b4ec8f4ab65
