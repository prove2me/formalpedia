-- Prove2me | Theorems.Thm_WassersteinLinOpt_Ball_exists_discrete_optimal_solution
-- name    : WassersteinLinOpt.Ball.exists_discrete_optimal_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T21:27:10.100267+00:00
-- url     : https://prove2.me/theorems/00a56bb5-2b92-4bea-8663-206419adb4e0
-- title:
--   Theorem 4 — existence of an optimal solution of (3) on at most $N+1$ atoms
-- statement:
--   Throughout, $(X,d)$ is a proper metric space (every closed ball is compact; such a space is complete and separable, hence Polish) with its Borel $\sigma$-algebra, and $p \ge 1$, $r > 0$ are real.
--
--   Let $\nu=\sum_{i=1}^N\alpha_i\,\delta_{y_i}$ be supported on $N$ distinct atoms $y_1,\dots,y_N\in X$ with weights $\alpha_i\ge0$, $\sum_i\alpha_i=1$. Let $f:X\to\mathbb R$ be upper semicontinuous with, for every $\mu\in\mathcal B_r(\nu)$, at least one of $\int[f]_+d\mu$ and $\int[-f]_+d\mu$ finite, and suppose there exist $x_0\in X$, $c>0$ and $p'\in(0,p)$ with
--
--   $$f(x)\le c\,[1+d^{p'}(x,x_0)]\qquad\text{for all }x\in X$$
--
--   (the conditions of Theorem 3).
--
--   **Theorem 4 (Existence of Discrete Optimal Solutions).** Problem (3) is optimized by a probability measure supported on at most $N+1$ atoms: there are $x_1,\dots,x_{N+1}\in X$ and $\beta_1,\dots,\beta_{N+1}\ge0$ with $\sum_j\beta_j=1$ such that
--
--   $$\mu^\star=\sum_{j=1}^{N+1}\beta_j\,\delta_{x_j}\in\mathcal B_r(\nu)\quad\text{and}\quad\int_X f\,d\mu^\star=\sup\Big\{\int_X f\,d\mu:\mu\in\mathcal B_r(\nu)\Big\}.$$
--
--   When $\nu$ is an empirical measure on $N$ samples, this reduces the infinite-dimensional problem (3) to a search over $N+1$ support points and weights.
--
--   **Formalization Note.** Theorem 3 also assumes that $\nu$ has a finite $p$-th moment; a finitely supported $\nu$ always does, so that hypothesis is omitted. The atom count is encoded as `Fin (N + 1)`-indexed points and `ℝ≥0` weights (points need not be distinct), not as mere finite support. The objective is the extended-real `quasiIntegral` and the optimal value is the `EReal` supremum `optimalValue p r ν f`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1114, Theorem 4

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_optimalValue

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Theorem 4 (Existence of Discrete Optimal Solutions), p. 1114. Let `ν = ∑_{i=1}^N αᵢ δ_{yᵢ}` be
supported on `N` distinct atoms, and let the conditions of Theorem 3 hold: `f` upper
semicontinuous and quasi-integrable under every `μ ∈ 𝓑_r(ν)`, and `f(x) ≤ c[1 + d^{p′}(x, x₀)]`
for all `x`, with `x₀ ∈ X`, `c > 0`, `p′ ∈ (0, p)`. (A finitely supported `ν` has a finite
`p`-th moment, so that condition is automatic.) Then problem (3) is optimized by a probability
measure `μ⋆ = ∑_{j=1}^{N+1} βⱼ δ_{xⱼ} ∈ 𝓑_r(ν)` supported on at most `N + 1` atoms. -/
theorem exists_discrete_optimal_solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r) {N : ℕ}
    (y : Fin N → X) (hy : Function.Injective y) (α : Fin N → ℝ≥0) (hα : ∑ i, α i = 1)
    (ν : ProbabilityMeasure X)
    (hν : (ν : Measure X) = ∑ i, (α i : ℝ≥0∞) • Measure.dirac (y i))
    (f : X → ℝ) (hf : UpperSemicontinuous f)
    (hquasi : ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) < ⊤ ∨
        ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X) < ⊤)
    (x₀ : X) (c p' : ℝ) (hc : 0 < c) (hp'0 : 0 < p') (hp'p : p' < p)
    (hgrowth : ∀ x : X, f x ≤ c * (1 + dist x x₀ ^ p')) :
    ∃ μ ∈ wassersteinBall p r ν,
      (∃ (x : Fin (N + 1) → X) (β : Fin (N + 1) → ℝ≥0), ∑ j, β j = 1 ∧
        (μ : Measure X) = ∑ j, (β j : ℝ≥0∞) • Measure.dirac (x j)) ∧
      quasiIntegral f (μ : Measure X) = optimalValue p r ν f := by sorry

end WassersteinLinOpt.Ball
