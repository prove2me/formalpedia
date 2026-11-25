-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_lambda
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsB_lambda
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:44.385845+00:00
-- url     : https://prove2.me/theorems/d260fd77-ac1e-5fe0-b069-9748d32c899c
-- title:
--   Y: bs B lambda
-- statement:
--   The Y construction uses the bs B lambda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepB.lean#L42-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepB.lean#L42-L62

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
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
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

theorem ReciprocityTheory.L2DbarEstimates.Y.bsB_lambda (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hLSE : LSEAll.{u} n) :
    SmoothR n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      Real.log (∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2)) ∧
    LeviNonneg n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      Real.log (∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2)) := by sorry
