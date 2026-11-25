-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_local_int
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.local_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:07.39067+00:00
-- url     : https://prove2.me/theorems/128bcaaf-ad50-4ec5-b864-c0a28108530e
-- title:
--   Weighted Atlas: local int
-- statement:
--   The Weighted Atlas construction uses the local int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZLocLower.lean#L117-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZLocLower.lean#L117-L248

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
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
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.local_int (A : WeightedAtlas n Y ι La) (hMVI : MVIntStatement n) (hn : 2 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {f : ι → Y → ℂ} (hf : A.IsSec la f) {T : ℕ}
    (hT : n + 1 ≤ T) {P : Y} (hP : P ∈ A.zeroSet s) (hv : A.VanishOrd f P (T - n)) :
    ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧
      ∫⁻ y in U, ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤ := by sorry
