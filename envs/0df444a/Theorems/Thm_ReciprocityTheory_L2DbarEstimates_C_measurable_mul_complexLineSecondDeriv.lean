-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_measurable_mul_complexLineSecondDeriv
-- name    : ReciprocityTheory.L2DbarEstimates.C.measurable_mul_complexLineSecondDeriv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:45.714005+00:00
-- url     : https://prove2.me/theorems/53185d15-f365-55c3-8dd6-f4693afd64c4
-- title:
--   C: measurable mul complex Line Second Deriv
-- statement:
--   The C construction uses the measurable mul complex Line Second Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L194-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L194-L215

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.measurable_mul_complexLineSecondDeriv {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) (e : V n) {χ : V n → ℂ} (hχ : Measurable χ)
    (hχΩ : ∀ z, χ z ≠ 0 → z ∈ Ω) : Measurable (fun z => χ z * complexLineSecondDeriv F z e) := by sorry
