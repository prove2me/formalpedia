-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_hv_c131b75442aa
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_hv_c131b75442aa
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:09.405246+00:00
-- url     : https://prove2.me/theorems/84c13f8d-d10a-49be-aa41-5eefe9c0807d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On hv c131b75442aa: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On hv c131b75442aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On hv c131b75442aa construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On hv c131b75442aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L371-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L371-L373

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
variable {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : IsEEMetric G)
include hG

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_hv_c131b75442aa : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hv G) (goodY ι ν κ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«contDiffOn_hv» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_hv_c131b75442aa
