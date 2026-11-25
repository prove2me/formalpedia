-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ypow_adbb8a5939c3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ypow_adbb8a5939c3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:47.379955+00:00
-- url     : https://prove2.me/theorems/c66fcf73-ae60-4a84-9adf-6bffc0bb0f25
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff ypow adbb8a5939c3: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff ypow adbb8a5939c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff ypow adbb8a5939c3 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff ypow adbb8a5939c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L365-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L365-L366

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
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ypow_adbb8a5939c3 (N : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ypow N : YPt ι ν κ → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«contDiff_ypow» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ypow_adbb8a5939c3
