-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_tendsto_of_continuous
-- name    : ReciprocityTheory.L2DbarEstimates.B.moll_tendsto_of_continuous
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:38.721652+00:00
-- url     : https://prove2.me/theorems/277b80c5-d1c2-4aa4-a31d-efe60597bcae
-- title:
--   B: moll tendsto of continuous
-- statement:
--   The B construction uses the moll tendsto of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollTendstoOfContinuous.lean#L8-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollTendstoOfContinuous.lean#L8-L57

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollTendstoOfContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem ReciprocityTheory.L2DbarEstimates.B.moll_tendsto_of_continuous (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι} {K : ι → Kernel E μ}
    (hK : Tendsto (fun i => (K i).r) l (𝓝 0)) {g : E → ℂ} (hgs : HasCompactSupport g)
    (hgc : Continuous g) : Tendsto (fun i => eLpNorm (moll (K i) g - g) 2 μ) l (𝓝 0) := by sorry
