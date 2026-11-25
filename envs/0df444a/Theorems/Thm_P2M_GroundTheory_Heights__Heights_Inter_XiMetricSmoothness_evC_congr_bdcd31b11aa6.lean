-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_congr_bdcd31b11aa6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_congr_bdcd31b11aa6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:34.93463+00:00
-- url     : https://prove2.me/theorems/a1552651-8969-4c12-abae-4821bbc7bd83
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness ev C congr bdcd31b11aa6: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness ev C congr bdcd31b11aa6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness ev C congr bdcd31b11aa6 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness ev C congr bdcd31b11aa6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L112-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L112-L125

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

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_congr_bdcd31b11aa6 {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) {w w' : (Σ k, ι k) → ℂ}
    (h : ∀ p : Σ k, ι k, a p.1 ≠ 0 → w p = w' p) : evC f w = evC f w' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«evC_congr» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_congr_bdcd31b11aa6
