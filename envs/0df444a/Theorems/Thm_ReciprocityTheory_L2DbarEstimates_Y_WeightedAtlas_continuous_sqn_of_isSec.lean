-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_continuous_sqn_of_isSec
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_sqn_of_isSec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:02:51.08909+00:00
-- url     : https://prove2.me/theorems/8e0766c4-c93a-570a-b619-8a90299080ba
-- title:
--   Weighted Atlas: continuous sqn of is Sec
-- statement:
--   The Weighted Atlas construction uses the continuous sqn of is Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxL.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxL.lean#L54-L57

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxK
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_sqn_of_isSec {N : ℕ} {la : La} {w : Fin N → ι → Y → ℂ} (hw : ∀ k, A.IsSec la (w k)) :
    Continuous (A.sqn la w) := by sorry
