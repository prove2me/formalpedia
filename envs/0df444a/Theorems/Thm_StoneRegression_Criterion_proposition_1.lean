-- Prove2me | Theorems.Thm_StoneRegression_Criterion_proposition_1
-- name    : StoneRegression.Criterion.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:56.477064+00:00
-- url     : https://prove2.me/theorems/b0a42037-42b7-48c9-8759-d4fe839c59b7
-- title:
--   Proposition 1, p. 607 — under (1)–(3), $E\sum_i|W_{ni}(X)||f(X_i)-f(X)|^r\to0$
-- statement:
--   Let $X, X_1, X_2,\dots$ be i.i.d. $\mathbb R^d$-valued with law $\mu$ and let $\{W_n\}$ be a sequence of Borel weights. Suppose that conditions (1)–(3) hold: there is $C\ge1$ with $E\sum_i|W_{ni}(X)|f(X_i)\le C\,Ef(X)$ for every nonnegative Borel $f$ and $n\ge1$; there is $D\ge1$ with $P(\sum_i|W_{ni}(X)|\le D)=1$ for $n\ge1$; and $\sum_i|W_{ni}(X)|\,I_{\{\|X_i-X\|>a\}}\to0$ in probability for every $a>0$.
--
--   Let $r\ge1$ and let $f$ be a Borel function on $\mathbb R^d$ with $E|f(X)|^r<\infty$. Then
--   $$\lim_{n\to\infty} E\sum_{i=1}^n |W_{ni}(X)|\,|f(X_i)-f(X)|^r = 0 .$$
--
--   This is the basic approximation step of the paper: weights concentrated near $X$ reproduce $f(X)$ in a weighted $L^r$ sense. It feeds Propositions 2 and 5 and thereby the sufficiency half of Theorem 1.
--
--   **Formalization Note.** The expectation is a lower Lebesgue integral in $[0,\infty]$ over the product law of $(X, X_1, X_2,\dots)$; $E|f(X)|^r<\infty$ is the corresponding lintegral against $\mu$. Joint Borel measurability of the weights is the series' standing assumption.
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 1, p. 607; proof pp. 607–608

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 1 (Stone 1977, p. 607). Under (1)–(3), for `r ≥ 1` and a Borel `f` with `E|f(X)|ʳ < ∞`,
`E ∑ᵢ |W_{ni}(X)| |f(Xᵢ) − f(X)|ʳ → 0`. Sample indices are 0-based. -/
theorem proposition_1 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (r : ℝ) (hr : 1 ≤ r) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f)
    (hfr : ∫⁻ x, ‖f x‖ₑ ^ r ∂μ < ∞) :
    Tendsto (fun n => ∫⁻ ω, ∑ i : Fin n,
        ‖wAt W n ω i‖ₑ * ‖f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ∂(xLaw μ)) atTop (𝓝 0) := by sorry

end StoneRegression.Criterion
