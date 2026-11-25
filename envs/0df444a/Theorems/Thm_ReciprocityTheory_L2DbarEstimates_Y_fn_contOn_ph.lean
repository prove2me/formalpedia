-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_contOn_ph
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fn_contOn_ph
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:52:51.62223+00:00
-- url     : https://prove2.me/theorems/bd56c31a-98b3-4297-9ca0-70c1cbd36bb3
-- title:
--   Y: fn cont On ph
-- statement:
--   The Y construction uses the fn cont On ph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullB.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullB.lean#L113-L117

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

theorem ReciprocityTheory.L2DbarEstimates.Y.fn_contOn_ph (la : La) (i : ι) : ContinuousOn (A.ph la i) (A.chart i).source := by sorry
