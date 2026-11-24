-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_dnorm_1d46eff272bd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_dnorm_1d46eff272bd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:15.494919+00:00
-- url     : https://prove2.me/theorems/6d1c1191-65b4-4736-8140-e2fba84378c8
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff dnorm 1d46eff272bd: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff dnorm 1d46eff272bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff dnorm 1d46eff272bd construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff dnorm 1d46eff272bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L362-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L362-L363

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

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_dnorm_1d46eff272bd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dnorm : YPt ι ν κ → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«contDiff_dnorm» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_dnorm_1d46eff272bd
