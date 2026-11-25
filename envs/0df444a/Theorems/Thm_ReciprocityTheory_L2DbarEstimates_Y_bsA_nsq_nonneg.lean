-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_nonneg
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsA_nsq_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:20:36.599082+00:00
-- url     : https://prove2.me/theorems/bb254b78-62b1-4a35-a68e-713a2898a4dc
-- title:
--   Y: bs A nsq nonneg
-- statement:
--   The Y construction uses the bs A nsq nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepA.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepA.lean#L139-L141

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
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
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.bsA_nsq_nonneg (la : La) (a : ι → Y → ℂ) (y : Y) : 0 ≤ A.nsq la a y := by sorry
