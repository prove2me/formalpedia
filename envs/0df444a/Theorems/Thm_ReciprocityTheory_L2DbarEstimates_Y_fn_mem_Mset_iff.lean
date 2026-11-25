-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_mem_Mset_iff
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fn_mem_Mset_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:44.863323+00:00
-- url     : https://prove2.me/theorems/c528b078-3acb-49d0-9e49-ba87b8136261
-- title:
--   Y: fn mem Mset iff
-- statement:
--   The Y construction uses the fn mem Mset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L133-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L133-L150

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
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

theorem ReciprocityTheory.L2DbarEstimates.Y.fn_mem_Mset_iff (hD : A.D0 L w w0 s) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    y ∈ A.Mset w0 s De ↔ fnHom De (w0 i y) (fun k => s k i y) ≠ 0 := by sorry
