-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_jz_trans
-- name    : ReciprocityTheory.L2DbarEstimates.Y.flL_jz_trans
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:07.688889+00:00
-- url     : https://prove2.me/theorems/730697ea-ad3e-4462-9e16-eb65d8fa5fef
-- title:
--   Y: fl L jz trans
-- statement:
--   The Y construction uses the fl L jz trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L97-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L97-L129

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
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
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

theorem ReciprocityTheory.L2DbarEstimates.Y.flL_jz_trans (hD : A.D0 L w w0 s) {y : Y} (hy : y ∈ A.Mset w0 s De) {i j : ι}
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    jz A w0 s j y = (jz A w0 s i y).comp
      (fderiv ℂ (A.chart i ∘ (A.chart j).symm) (A.chart j y)) := by sorry
