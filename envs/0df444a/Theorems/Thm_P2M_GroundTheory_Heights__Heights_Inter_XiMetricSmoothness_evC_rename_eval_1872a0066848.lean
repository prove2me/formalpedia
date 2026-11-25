-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_rename_eval_1872a0066848
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_rename_eval_1872a0066848
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:55.921067+00:00
-- url     : https://prove2.me/theorems/bc9e7727-b710-4b96-b221-1b9eeda5ee16
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness ev C rename eval 1872a0066848: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness ev C rename eval 1872a0066848
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness ev C rename eval 1872a0066848 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness ev C rename eval 1872a0066848 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L141-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_rename_eval_1872a0066848 {K' : Type*} {ι' : K' → Type*} (e : (Σ k, ι k) → (Σ k, ι' k)) (f : MRing ι)
    (z : (Σ k, ι' k) → ℂ) : eval z (map (Int.castRingHom ℂ) (rename e f)) = evC f (fun p => z (e p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«evC_rename_eval» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_rename_eval_1872a0066848
