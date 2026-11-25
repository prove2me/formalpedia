-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_inverse
-- name    : ReciprocityTheory.L2DbarEstimates.Y.flL_inverse
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:10:04.042888+00:00
-- url     : https://prove2.me/theorems/144fb8cb-8926-475a-8840-e8834086ce90
-- title:
--   Y: fl L inverse
-- statement:
--   The Y construction uses the fl L inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L193-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L193-L238

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

theorem ReciprocityTheory.L2DbarEstimates.Y.flL_inverse {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n))
    (he : IsChart n (flatStein A hD hF).z e) (v : V n) (hv : v ∈ e.target) (i : ι)
    (hi : ((e.symm v : A.Mset w0 s De) : Y) ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : Y)) v ∧
      (∀ᶠ v' in 𝓝 v, ((e.symm v' : A.Mset w0 s De) : Y) ∈ (A.chart i).source) ∧
      ∀ ξ : V n, fderiv ℂ (fun v' => A.chart i (e.symm v' : Y)) v
        (jz A w0 s i (e.symm v : Y) ξ) = ξ := by sorry
