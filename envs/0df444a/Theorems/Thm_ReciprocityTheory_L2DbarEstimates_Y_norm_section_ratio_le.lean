-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_norm_section_ratio_le
-- name    : ReciprocityTheory.L2DbarEstimates.Y.norm_section_ratio_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:48.015989+00:00
-- url     : https://prove2.me/theorems/783c95a4-6d80-4328-a07b-9a7916c8d23e
-- title:
--   Y: norm section ratio le
-- statement:
--   The Y construction uses the norm section ratio le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/VanishingOrderTransfer.lean#L94-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/VanishingOrderTransfer.lean#L94-L149

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_VanishingOrderTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.norm_section_ratio_le {N' : ℕ} (A : WeightedAtlas n Y ι La) (L : La) (m : ℕ)
    (w : Fin N' → ι → Y → ℂ) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (Nsec : ι → Y → ℂ)
    (C1 C2 : ℝ) (h1 : ∀ y, A.nsq (m • L) Nsec y ≤ C1 * A.sqn L w y ^ m)
    (h2 : ∀ y, A.sqn L w y ≤ C2 * (A.nsq L w0 y + A.sqn L s y)) (y : Y)
    (hy0 : w0 (A.pick y) y ≠ 0) :
    ‖Nsec (A.pick y) y / w0 (A.pick y) y ^ m‖ ≤
      Real.sqrt (max C1 0 * |C2| ^ m) * (1 + ‖A.zmap w0 s y‖ ^ 2) ^ ((m : ℝ) / 2) := by sorry
