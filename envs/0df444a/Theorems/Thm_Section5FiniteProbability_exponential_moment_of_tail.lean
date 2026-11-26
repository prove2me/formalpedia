-- Prove2me | Theorems.Thm_Section5FiniteProbability_exponential_moment_of_tail
-- name    : Section5FiniteProbability.exponential_moment_of_tail
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:19:47.473802+00:00
-- url     : https://prove2.me/theorems/0d8e3943-706a-440c-89ba-f547c6781a31
-- title:
--   An exponential tail gives an exponential moment
-- statement:
--   Let $\mu$ be a probability measure on a finite measurable space with measurable singletons, and let $Y\ge0$. Suppose $\mu\{Y\ge t\}\le3e^{-t/4}$ for every $t\ge0$. Then
--
--   $$\int e^{Y/512}\,d\mu\le\frac{130}{127}.$$
--
--   This converts the stated tail estimate into a concrete exponential-moment bound.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5FiniteExponentialTail.lean, lines 9–58.

import Mathlib
set_option autoImplicit false
namespace Section5FiniteProbability
end Section5FiniteProbability
open Section5FiniteProbability
open MeasureTheory Set

theorem Section5FiniteProbability.exponential_moment_of_tail {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : ∀ x, 0 ≤ Y x)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {x | t ≤ Y x} ≤ 3*Real.exp (-t/4)) :
    (∫ x, Real.exp (Y x/512) ∂μ) ≤ 130/127 := by sorry
