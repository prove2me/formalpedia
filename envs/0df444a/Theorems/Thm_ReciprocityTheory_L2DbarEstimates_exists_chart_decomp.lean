-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_decomp
-- name    : ReciprocityTheory.L2DbarEstimates.exists_chart_decomp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:13.489008+00:00
-- url     : https://prove2.me/theorems/c649c102-59c3-5c6e-bd5e-ae7077ee88a5
-- title:
--   L2 Dbar Estimates: exists chart decomp
-- statement:
--   The L2 Dbar Estimates construction uses the exists chart decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L176-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L176-L192

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

theorem ReciprocityTheory.L2DbarEstimates.exists_chart_decomp {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Ck n z 1 g) (hc : HasCompactSupport g) :
    ∃ (N : ℕ) (e : Fin N → OpenPartialHomeomorph M (V n)) (h : Fin N → M → ℂ),
      (∀ i, IsChart n z (e i)) ∧ (∀ i, Ck n z 1 (h i)) ∧ (∀ i, HasCompactSupport (h i)) ∧
      (∀ i, tsupport (h i) ⊆ (e i).source) ∧ g = fun x => ∑ i, h i x := by sorry
