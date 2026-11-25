-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_chart_extend
-- name    : ReciprocityTheory.L2DbarEstimates.chart_extend
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:53.430045+00:00
-- url     : https://prove2.me/theorems/b0d0406c-e3e8-417e-b417-4d0d50cde2af
-- title:
--   L2 Dbar Estimates: chart extend
-- statement:
--   The L2 Dbar Estimates construction uses the chart extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L62-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L62-L89

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.chart_extend {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (h : M → ℂ) (hh : Ck n z 1 h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ e.source) :
    ∃ H : V n → ℂ, ContDiff ℝ 1 H ∧ HasCompactSupport H ∧
      (∀ y ∈ e.target, H =ᶠ[𝓝 y] h ∘ e.symm) ∧ (∀ y ∉ e.target, H =ᶠ[𝓝 y] fun _ => 0) := by sorry
