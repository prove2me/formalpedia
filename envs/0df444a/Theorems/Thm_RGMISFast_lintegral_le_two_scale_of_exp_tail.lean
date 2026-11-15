-- Prove2me | Theorems.Thm_RGMISFast_lintegral_le_two_scale_of_exp_tail
-- name    : RGMISFast.lintegral_le_two_scale_of_exp_tail
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T00:46:13.950205+00:00
-- url     : https://prove2.me/theorems/4cc72965-3dfc-4125-b176-0f51983bbc3d
-- title:
--   Integrating a shifted exponential tail gives expectation at most twice the scale
-- statement:
--   Let X be a measurable natural-valued random variable on a probability space and let F>0. If for every h≥0,
--
--   $$\Pr[X>F(1+h)]\le e^{-h},$$
--
--   then
--
--   $$\mathbb E[X]\le 2F.$$
--
--   This is the general tail-integration step in the proof of Theorem 1.1, stated independently of graphs. The expectation is represented by the nonnegative Lebesgue integral.
-- source:
--   Randomized Greedy MIS Is Fast at Every Node, proof of Theorem 1.1, p.17, displayed tail-integration formula. Generalization from the query counter to any measurable natural-valued random variable.

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem RGMISFast.lintegral_le_two_scale_of_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℕ) (hX : Measurable X)
    (F : ℝ) (hF : 0 < F)
    (htail : ∀ h : ℝ, 0 ≤ h → μ {ω | F * (1 + h) < (X ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-h))) :
    ∫⁻ ω, (X ω : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (2 * F) := by sorry
