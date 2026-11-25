-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_continuousOn_sec
-- name    : ReciprocityTheory.L2DbarEstimates.Y.continuousOn_sec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:39.08541+00:00
-- url     : https://prove2.me/theorems/d33c57aa-a08b-532b-80bb-f73f13b123cc
-- title:
--   Y: continuous On sec
-- statement:
--   The Y construction uses the continuous On sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContinuousOnSec.lean#L172-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContinuousOnSec.lean#L172-L181

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u

theorem ReciprocityTheory.L2DbarEstimates.Y.continuousOn_sec {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*}
    [AddCommGroup La] {A : WeightedAtlas n Y ι La} {la : La} {f : ι → Y → ℂ}
    (hf : A.IsSec la f) (i : ι) : ContinuousOn (f i) (A.chart i).source := by sorry
