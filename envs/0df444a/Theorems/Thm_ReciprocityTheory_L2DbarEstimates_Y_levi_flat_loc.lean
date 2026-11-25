-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_levi_flat_loc
-- name    : ReciprocityTheory.L2DbarEstimates.Y.levi_flat_loc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:36.611572+00:00
-- url     : https://prove2.me/theorems/2c6fb586-1a34-4a49-8bda-4fe6692de2ae
-- title:
--   Y: levi flat loc
-- statement:
--   The Y construction uses the levi flat loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L304-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L304-L344

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

theorem ReciprocityTheory.L2DbarEstimates.Y.levi_flat_loc {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (φ : Y → ℝ) (i : ι) (x : A.Mset w0 s De)
    (hx : (x : Y) ∈ (A.chart i).source)
    (hφ : ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x)) (ξ : Fin n → ℂ) :
    A.leviAt i φ x ξ =
      (Levi n (flatStein A hD hF).z (fun y : A.Mset w0 s De => φ y) x
        (fun k => jz A w0 s i x (WithLp.toLp 2 ξ) k)).re := by sorry
