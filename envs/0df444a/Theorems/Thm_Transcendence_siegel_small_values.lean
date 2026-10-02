-- Prove2me | Theorems.Thm_Transcendence_siegel_small_values
-- name    : Transcendence.siegel_small_values
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:57.910302+00:00
-- url     : https://prove2.me/theorems/22592b42-9f29-44cd-a4a9-45463409e037
-- title:
--   An auxiliary function with integer coefficients, small on a polydisc (Thue–Siegel, Proposition 4.10)
-- statement:
--   Let $n = |\iota| \ge 1$ and let $\varphi_\lambda$ ($\lambda \in \Lambda$) be entire functions on $\mathbb{C}^\iota$. Let $N, U, V, r > 0$ and $R$ with $W = N + U + V \ge 12n^2$ and $er \le R \le re^{W/6}$. Suppose $|\varphi_\lambda| \le B_\lambda$ on the polydisc of radius $R$, with $\sum_\lambda B_\lambda \le e^{U}$, and
--
--   $$(2W)^{n+1} \le |\Lambda|\, N\, \bigl(\log(R/r)\bigr)^{n}.$$
--
--   Then there are integers $p_\lambda$, not all zero, with $|p_\lambda| \le e^{N}$, such that $|\sum_\lambda p_\lambda\varphi_\lambda| \le e^{-V}$ on the polydisc of radius $r$.
--
--   This is Proposition 4.10 of Waldschmidt's book, proved by Dirichlet's box principle (Thue–Siegel) applied to the Taylor coefficients at the origin, with Cauchy's inequality in place of Parseval's.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Proposition 4.10 with Lemmas 4.11–4.13 (pp. 131–136). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **An auxiliary function with small values** (Waldschmidt, *Diophantine Approximation on Linear Algebraic
Groups*, Prop. 4.10, proved with Dirichlet's box principle, Lemmas 4.11–4.13; Parseval may be replaced by Cauchy).
Let `n = |ι| ≥ 1`, let `φ_λ` (`λ ∈ Λ`, `L = |Λ|`) be entire functions on `ℂ^ι`, and let `N, U, V, r, R > 0` with
`W = N + U + V ≥ 12n²` and `e ≤ R/r ≤ e^{W/6}`. Assume `|φ_λ| ≤ B_λ` on the closed polydisc of radius `R` (the
sup-norm ball), with `Σ_λ B_λ ≤ e^U`, and `(2W)^{n+1} ≤ L·N·(log(R/r))ⁿ`. Then there are integers `p_λ`, not all
zero, with `|p_λ| ≤ e^N`, such that `|Σ_λ p_λ φ_λ| ≤ e^{-V}` on the closed polydisc of radius `r`. -/
theorem siegel_small_values {ι Λ : Type*} [Fintype ι] [Fintype Λ] (hι : 0 < Fintype.card ι)
    (φ : Λ → (ι → ℂ) → ℂ) (hφ : ∀ l, AnalyticOnNhd ℂ (φ l) Set.univ)
    {N U V r R : ℝ} (hN : 0 < N) (hU : 0 < U) (hV : 0 < V) (hr : 0 < r)
    (hW : 12 * (Fintype.card ι : ℝ) ^ 2 ≤ N + U + V)
    (hRe : Real.exp 1 * r ≤ R) (hRW : R ≤ r * Real.exp ((N + U + V) / 6))
    (B : Λ → ℝ) (hB : ∀ l, ∀ z ∈ Metric.closedBall (0 : ι → ℂ) R, ‖φ l z‖ ≤ B l)
    (hBU : ∑ l, B l ≤ Real.exp U)
    (hmain : (2 * (N + U + V)) ^ (Fintype.card ι + 1) ≤
      Fintype.card Λ * N * Real.log (R / r) ^ Fintype.card ι) :
    ∃ p : Λ → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp N) ∧
      ∀ z ∈ Metric.closedBall (0 : ι → ℂ) r, ‖∑ l, (p l : ℂ) * φ l z‖ ≤ Real.exp (-V) := by
  sorry

end Transcendence
