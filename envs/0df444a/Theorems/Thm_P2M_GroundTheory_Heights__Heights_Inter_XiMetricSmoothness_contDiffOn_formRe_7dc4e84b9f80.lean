-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_formRe_7dc4e84b9f80
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_formRe_7dc4e84b9f80
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:25:38.439041+00:00
-- url     : https://prove2.me/theorems/6793efc5-eaea-4caa-bce0-75ef5a28fb86
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On form Re 7dc4e84b9f80: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On form Re 7dc4e84b9f80
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On form Re 7dc4e84b9f80 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On form Re 7dc4e84b9f80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L85-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L85-L93

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {n : WithTop ℕ∞}

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_formRe_7dc4e84b9f80 {ι' : Type*} [Fintype ι'] {M : E → Matrix ι' ι' ℂ} {u v : E → ι' → ℂ}
    (hM : ∀ p q, ContDiffOn ℝ n (fun x => M x p q) s) (hu : ∀ p, ContDiffOn ℝ n (fun x => u x p) s)
    (hv : ∀ p, ContDiffOn ℝ n (fun x => v x p) s) :
    ContDiffOn ℝ n (fun x => (star (u x) ⬝ᵥ (M x *ᵥ v x)).re) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«contDiffOn_formRe» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_formRe_7dc4e84b9f80
