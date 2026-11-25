-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_levi_psD
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.levi_psD
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:36:39.96356+00:00
-- url     : https://prove2.me/theorems/c6dbf481-2d57-4bbc-8815-b3aefc9fa4e8
-- title:
--   Weighted Atlas: levi ps D
-- statement:
--   The Weighted Atlas construction uses the levi ps D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxC.lean#L90-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxC.lean#L90-L203

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.levi_psD {N : ℕ} {L la : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (hPosL : A.Pos L fun _ => 0)
    {ps1 : Y → ℝ} (hps1 : A.SmoothFn ps1) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hLevi : ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      2 * η * A.leviAt i (A.ph L i) y ξ ≤
        A.leviAt i (fun x => A.ph (la - n • L) i x + ps1 x) y ξ)
    (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    η * A.leviAt i (A.ph L i) y ξ ≤
      A.leviAt i (fun x => A.ph la i x + A.psD L w s ps1 η δ x) y ξ := by sorry
