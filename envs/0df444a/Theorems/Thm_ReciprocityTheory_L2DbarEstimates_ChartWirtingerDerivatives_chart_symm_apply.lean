-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_chart_symm_apply
-- name    : ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.chart_symm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:10.124149+00:00
-- url     : https://prove2.me/theorems/c69f38ea-22a9-49e0-8de9-c52c76f32931
-- title:
--   Chart Wirtinger Derivatives: chart symm apply
-- statement:
--   The Chart Wirtinger Derivatives construction uses the chart symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L32-L36

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.chart_symm_apply {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M) (hx : x ∈ e.source) :
    e.symm (z x) = x := by sorry
