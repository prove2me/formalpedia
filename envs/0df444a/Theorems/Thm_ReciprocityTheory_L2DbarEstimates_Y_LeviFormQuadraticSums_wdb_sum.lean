-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LeviFormQuadraticSums_wdb_sum
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.wdb_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:22.339737+00:00
-- url     : https://prove2.me/theorems/46d89a29-5d9e-4fc3-970e-84b2b076bc6c
-- title:
--   Levi Form Quadratic Sums: wdb sum
-- statement:
--   The Levi Form Quadratic Sums construction uses the wdb sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeDA.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeDA.lean#L17-L21

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.wdb_sum {ι : Type*} (s : Finset ι) {g : ι → V n → ℂ} {y : V n}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) y) (j : Fin n) :
    wdb n j (fun w => ∑ i ∈ s, g i w) y = ∑ i ∈ s, wdb n j (g i) y := by sorry
