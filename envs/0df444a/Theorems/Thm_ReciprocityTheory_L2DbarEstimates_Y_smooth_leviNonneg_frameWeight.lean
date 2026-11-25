-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_smooth_leviNonneg_frameWeight
-- name    : ReciprocityTheory.L2DbarEstimates.Y.smooth_leviNonneg_frameWeight
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:27:33.331799+00:00
-- url     : https://prove2.me/theorems/a2d10e3a-1db7-4ed5-be8a-459c082b1752
-- title:
--   Y: smooth levi Nonneg frame Weight
-- statement:
--   The Y construction uses the smooth levi Nonneg frame Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepB.lean#L211-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepB.lean#L211-L235

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
variable {mu0 : La} {σ : ι → Y → ℂ}

theorem ReciprocityTheory.L2DbarEstimates.Y.smooth_leviNonneg_frameWeight (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hLSE : LSEAll.{u} n)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0)) :
    SmoothR n (flatStein A hD hF).z (fun x : A.Mset w0 s De => bsPh0 A w w0 s mu0 σ x) ∧
    LeviNonneg n (flatStein A hD hF).z (fun x : A.Mset w0 s De => bsPh0 A w w0 s mu0 σ x) := by sorry
