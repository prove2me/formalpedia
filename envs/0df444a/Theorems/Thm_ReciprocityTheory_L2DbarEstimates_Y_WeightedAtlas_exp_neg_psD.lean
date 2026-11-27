-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_exp_neg_psD
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.exp_neg_psD
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:30:16.892977+00:00
-- url     : https://prove2.me/theorems/c2c7e410-15db-4984-ba41-b60cfe4fd2ef
-- title:
--   Weighted Atlas: exp neg ps D
-- statement:
--   The Weighted Atlas construction uses the exp neg ps D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxC.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxC.lean#L81-L88

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

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.exp_neg_psD {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (ps1 : Y → ℝ) (η : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (y : Y) : Real.exp (-A.psD L w s ps1 η δ y) =
      Real.exp (-ps1 y) * A.sqn L w y ^ (-η) * (A.sqn L s y + δ) ^ (-(n : ℝ)) := by sorry
