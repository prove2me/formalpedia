-- Prove2me | Theorems.Thm_StoneRegression_Criterion_proposition_5
-- name    : StoneRegression.Criterion.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:48.987977+00:00
-- url     : https://prove2.me/theorems/665b47fe-209e-4804-9f24-88762a859bfc
-- title:
--   Proposition 5, p. 609 — under (1)–(4), $\sum_i W_{ni}(X)f(X_i)\to f(X)$ in $L^r$
-- statement:
--   Let $X, X_1, X_2,\dots$ be i.i.d. $\mathbb R^d$-valued with law $\mu$ and let $\{W_n\}$ be a sequence of Borel weights satisfying conditions (1)–(4) of Theorem 1: (1) with some $C\ge1$, (2) with some $D\ge1$, the localization condition (3), and $\sum_i W_{ni}(X)\to1$ in probability (4).
--
--   If $r\ge1$ and $f$ is a Borel function on $\mathbb R^d$ with $E|f(X)|^r<\infty$, then $\sum_i W_{ni}(X)f(X_i)\to f(X)$ in $L^r$:
--   $$\lim_{n\to\infty} E\,\Big|\sum_{i=1}^n W_{ni}(X)f(X_i) - f(X)\Big|^r = 0 .$$
--
--   This is the noise-free version of consistency: with $f(x) = E(Y\mid X=x)$ it handles the bias part of $\hat E_n(Y\mid X) - E(Y\mid X)$ in the proof of Theorem 1.
--
--   **Formalization Note.** The $L^r$ distance is a lower Lebesgue integral in $[0,\infty]$, as is $E|f(X)|^r$. Weights are assumed jointly Borel (standing assumption).
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 5, p. 609

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 5 (Stone 1977, p. 609). Under (1)–(4), for `r ≥ 1` and a Borel `f` with `E|f(X)|ʳ < ∞`,
`∑ᵢ W_{ni}(X) f(Xᵢ) → f(X)` in `Lʳ`, i.e. `E|∑ᵢ W_{ni}(X) f(Xᵢ) − f(X)|ʳ → 0`. -/
theorem proposition_5 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (h4 : Cond4 μ W)
    (r : ℝ) (hr : 1 ≤ r) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f)
    (hfr : ∫⁻ x, ‖f x‖ₑ ^ r ∂μ < ∞) :
    Tendsto (fun n => ∫⁻ ω,
        ‖∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ∂(xLaw μ)) atTop (𝓝 0) := by sorry

end StoneRegression.Criterion
