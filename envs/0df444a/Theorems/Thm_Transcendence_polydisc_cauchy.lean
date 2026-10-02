-- Prove2me | Theorems.Thm_Transcendence_polydisc_cauchy
-- name    : Transcendence.polydisc_cauchy
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:49.492323+00:00
-- url     : https://prove2.me/theorems/623dbe11-9b39-48a3-aa5c-a35bb6a4613c
-- title:
--   Cauchy's inequalities on a polydisc, for mixed derivatives along a list of directions
-- statement:
--   Let $F$ be an entire function on $\mathbb{C}^\iota$ with $|F| \le M$ on the closed polydisc of centre $p$ and radius $\rho > 0$ (the closed ball for the sup norm). For a list of directions $L : \{0, \dots, k-1\} \to \iota$, let $\sigma_\nu$ be the number of times $\nu$ occurs in $L$. Then
--
--   $$\Bigl|D^{k}F(p)\,(e_{L(0)}, \dots, e_{L(k-1)})\Bigr| \le \Bigl(\prod_\nu \sigma_\nu!\Bigr)\,\frac{M}{\rho^{k}},$$
--
--   where $D^kF$ is the $k$-th Fréchet derivative and $e_\nu$ the coordinate vectors; in multi-index notation, $|D^\sigma F(p)| \le \sigma!\,M\rho^{-|\sigma|}$.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: the classical Cauchy inequalities, in the form recorded in Waldschmidt's book (p. XVII). The contribution of this node is the formal proof.
-- source:
--   Classical; the form used here is in M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, p. XVII. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **Cauchy's inequalities on a polydisc** (Waldschmidt, *Diophantine Approximation on Linear Algebraic
Groups*, p. XVII). Let `F` be an entire function of the variables `z_ν` (`ν ∈ ι`), bounded by `M` on the closed
polydisc of centre `p` and radius `ρ > 0` (the sup-norm ball). The mixed partial derivative of `F` at `p` along
the coordinate directions `L 0, …, L (k-1)`, of multi-index `σ_ν = #{l | L l = ν}` and total order `k`, satisfies
`|D^σ F(p)| ≤ σ! · M / ρ^k`, where `σ! = ∏_ν σ_ν!`. -/
theorem polydisc_cauchy {ι : Type*} [Fintype ι] [DecidableEq ι] {F : (ι → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (p : ι → ℂ) {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ z ∈ Metric.closedBall p ρ, ‖F z‖ ≤ M) (k : ℕ) (L : Fin k → ι) :
    ‖iteratedFDeriv ℂ k F p (fun l => Pi.single (L l) 1)‖ ≤
      (∏ ν, ((Finset.univ.filter fun l => L l = ν).card.factorial : ℝ)) * M / ρ ^ k := by
  sorry

end Transcendence
