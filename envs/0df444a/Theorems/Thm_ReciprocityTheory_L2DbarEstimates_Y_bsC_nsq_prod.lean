-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsC_nsq_prod
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsC_nsq_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:40:32.141083+00:00
-- url     : https://prove2.me/theorems/d1daac3b-498b-4e28-8e87-108e5617b036
-- title:
--   Y: bs C nsq prod
-- statement:
--   The Y construction uses the bs C nsq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepC.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepC.lean#L37-L45

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
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

theorem ReciprocityTheory.L2DbarEstimates.Y.bsC_nsq_prod (la L : La) (m : ℕ) (q u v : ι → Y → ℂ) (c : ℂ) (y : Y)
    (hq : q (A.pick y) y = c * (u (A.pick y) y * v (A.pick y) y ^ m)) :
    A.nsq (la + m • L) q y = ‖c‖ ^ 2 * A.nsq la u y * A.nsq L v y ^ m := by sorry
