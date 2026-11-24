-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_normSq_coord_b2ec97168040
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_normSq_coord_b2ec97168040
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:04.776978+00:00
-- url     : https://prove2.me/theorems/904d9a48-acea-48f9-9f2b-9ff759c6d1f0
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff norm Sq coord b2ec97168040: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff norm Sq coord b2ec97168040
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff norm Sq coord b2ec97168040 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff norm Sq coord b2ec97168040 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L355-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L355-L357

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

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_normSq_coord_b2ec97168040 (p : Σ k, T.yyIdx ι ν κ k) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : YPt ι ν κ => ‖w p‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«contDiff_normSq_coord» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_normSq_coord_b2ec97168040
