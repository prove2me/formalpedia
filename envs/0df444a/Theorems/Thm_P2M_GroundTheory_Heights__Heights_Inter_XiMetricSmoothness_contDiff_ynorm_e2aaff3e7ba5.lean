-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ynorm_e2aaff3e7ba5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ynorm_e2aaff3e7ba5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:49.86036+00:00
-- url     : https://prove2.me/theorems/44c9c206-443d-5bbf-b79b-5b22f7f3a590
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff ynorm e2aaff3e7ba5: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff ynorm e2aaff3e7ba5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff ynorm e2aaff3e7ba5 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff ynorm e2aaff3e7ba5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L359-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L359-L360

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

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ynorm_e2aaff3e7ba5 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ynorm : YPt ι ν κ → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«contDiff_ynorm» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ynorm_e2aaff3e7ba5
