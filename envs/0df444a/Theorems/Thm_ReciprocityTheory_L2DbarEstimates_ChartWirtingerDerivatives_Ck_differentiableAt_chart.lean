-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_Ck_differentiableAt_chart
-- name    : ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.Ck.differentiableAt_chart
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:58.474836+00:00
-- url     : https://prove2.me/theorems/321cfcc4-7e83-4680-bba3-9af686bb3ae4
-- title:
--   Ck: differentiable At chart
-- statement:
--   The Ck construction uses the differentiable At chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L38-L43

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

theorem ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.Ck.differentiableAt_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → ℂ) (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (x : M) (hx : x ∈ e.source) :
    DifferentiableAt ℝ (f ∘ e.symm) (z x) := by sorry
