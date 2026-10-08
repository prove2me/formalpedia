-- Prove2me | Theorems.Thm_StoneRegression_NearestNeighbor_proposition_11
-- name    : StoneRegression.NearestNeighbor.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:39.436233+00:00
-- url     : https://prove2.me/theorems/11433b1c-1624-4f9a-aef0-cab34234f493
-- title:
--   Proposition 11, p. 613 — nearest neighbor weights satisfy condition (1) with C = β(d, a/b)
-- statement:
--   Let $X, X_1, X_2, \dots$ be i.i.d. in $\mathbb R^d$ with law $\mu$, let $\{s_n\}$ be a regular sequence of scales with constants $0 < a \le b$ in (7), let $n \ge 1$ and let $W_n$ be the nearest neighbor probability weight function (8) of a coefficient row $c_n$. If $f$ is a nonnegative Borel function on $\mathbb R^d$ with $E f(X) < \infty$, then
--   $$E \sum_{i=1}^n W_{ni}(X) f(X_i) \le \beta(d, a/b)\, E f(X).$$
--
--   This is condition (1) of Stone's consistency criterion for nearest neighbor weights, with a constant that depends only on the dimension and the ratio $a/b$ — in particular not on $n$ nor on the distribution of $X$.
--
--   **Formalization Note** The expectations are lower Lebesgue integrals in $[0,\infty]$, and $f$ takes values in $[0,\infty)$. The hypothesis is the section's standing assumption that the scales are regular (p. 599), which contains (7) with the constants $a, b$ of the statement and the measurability of the scales.
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 11, p. 613; proof p. 613 and pp. 613–615 (via Proposition 12)

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem proposition_11 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (s : ScaleSeq d) (a b : ℝ) (hs : IsRegular μ s a b)
    (c : ℕ → ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : IsCoeffRow c n)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hf : Measurable f) (hfi : ∫⁻ x, (f x : ℝ≥0∞) ∂μ < ∞) :
    ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (StoneRegression.Criterion.wAt (nnWeights c s) n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) ≤
      (beta d (a / b) : ℝ≥0∞) * ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by sorry

end StoneRegression.NearestNeighbor
