-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_green_dir
-- name    : ReciprocityTheory.L2DbarEstimates.C.green_dir
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:14.22627+00:00
-- url     : https://prove2.me/theorems/eea183ed-d047-56d3-9aef-768d17ddab02
-- title:
--   C: green dir
-- statement:
--   The C construction uses the green dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L121-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L121-L262

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
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

theorem ReciprocityTheory.L2DbarEstimates.C.green_dir {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {T : Set (V n)} (hT : IsCompact T) (hTΩ : T ⊆ Ω) {ψ : V n → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψT : tsupport ψ ⊆ T) {ε : ℝ} (hε : 0 < ε) (e : V n) (μ : ℂ) (hμ : ‖μ‖ = 1)
    {M A B : ℝ} (hM : ∀ z ∈ T, ‖F z‖ ≤ M) (hA : ∀ z ∈ T, ‖fderiv ℂ F z e‖ ≤ A)
    (hB : ∀ z ∈ T, ‖complexLineSecondDeriv F z e‖ ≤ B) :
    Integrable (fun z => ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) ∧
    Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e) *
      cutP ε (‖F z‖ ^ 2)) ∧
    Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e)) ∧
    (∀ z ∉ T, fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e) = 0) ∧
    ∫ z, ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ) =
      ∫ z, fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e) * cutP ε (‖F z‖ ^ 2) := by sorry
