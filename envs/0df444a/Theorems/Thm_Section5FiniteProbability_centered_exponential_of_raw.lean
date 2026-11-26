-- Prove2me | Theorems.Thm_Section5FiniteProbability_centered_exponential_of_raw
-- name    : Section5FiniteProbability.centered_exponential_of_raw
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:23:31.834298+00:00
-- url     : https://prove2.me/theorems/0f552e60-2e6a-5bfe-adf0-c89d12a583ba
-- title:
--   Centering preserves a fixed exponential-moment bound
-- statement:
--   Let $\Omega$ be a finite measurable space with measurable singletons, let $\mu$ be a probability measure on it, and let $Y:\Omega\to\mathbb R$. Suppose $\mathbb E_\mu[e^{|Y|/512}]\le130/127$ and $|\mathbb E_\mu Y|\le3$. Then
--
--   $$
--   \mathbb E_\mu\!\left[e^{|Y-\mathbb E_\mu Y|/512}\right]\le2.
--   $$
--
--   This converts the stated raw exponential-moment and mean bounds into a centered exponential-moment bound.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5FiniteCenteredExponential.lean, Section5FiniteProbability.centered_exponential_of_raw, lines 9–29.

import Mathlib
set_option autoImplicit false
namespace Section5FiniteProbability
end Section5FiniteProbability
open Section5FiniteProbability
open MeasureTheory

theorem Section5FiniteProbability.centered_exponential_of_raw {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hraw : (∫ x, Real.exp (|Y x|/512) ∂μ) ≤ 130/127)
    (hmean : |∫ x, Y x ∂μ| ≤ 3) :
    (∫ x, Real.exp (|Y x-(∫ y, Y y ∂μ)|/512) ∂μ) ≤ 2 := by sorry
