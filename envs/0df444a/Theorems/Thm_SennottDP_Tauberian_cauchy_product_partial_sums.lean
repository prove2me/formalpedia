-- Prove2me | Theorems.Thm_SennottDP_Tauberian_cauchy_product_partial_sums
-- name    : SennottDP.Tauberian.cauchy_product_partial_sums
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:05:57.134071+00:00
-- url     : https://prove2.me/theorems/5b724600-d3e8-471b-a3ab-cf30924e117c
-- title:
--   Eq. (A.31) — (Σα^n)(Σα^n u_n) = Σ α^n w_{n+1} = U(α)/(1−α)
-- statement:
--   Let $u_n \in [0,\infty)$ for every $n$, with radius of convergence $R \ge 1$, and let $w_n = \sum_{k=0}^{n-1} u_k$. For every $\alpha \in [0,1)$,
--   $$\Big(\sum_{n=0}^{\infty} \alpha^n\Big)\Big(\sum_{n=0}^{\infty} \alpha^n u_n\Big) = \sum_{n=0}^{\infty} \alpha^n w_{n+1} = \frac{U(\alpha)}{1-\alpha}.$$
--
--   This expresses the Abel mean through the partial sums: $(1-\alpha)U(\alpha) = (1-\alpha)^2 \sum_n \alpha^n w_{n+1}$, the identity on which the Abelian inequalities rest.
--
--   **Formalization Note** All sums are in $[0,\infty]$, so both sides may be $+\infty$ (possible when $R = 1$). The hypotheses $u_n < \infty$ and $R \ge 1$ are those in force at this point of the book's proof; the identity itself holds in $[0,\infty]$ without them.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 283, Eq. (A.31) (proof of Theorem A.4.2)

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 283, Eq. (A.31): if all terms `u_n` are finite and the radius of
convergence satisfies `R ≥ 1`, then for `α ∈ [0, 1)`
`(∑ α^n)(∑ α^n u_n) = ∑_{n ≥ 0} α^n w_{n+1}`, and this power series sums to `U(α)/(1 − α)`. -/
theorem cauchy_product_partial_sums (u : ℕ → ℝ≥0∞) (hfin : ∀ n, u n ≠ ⊤)
    (hR : 1 ≤ radius u) (α : ℝ≥0) (hα : α < 1) :
    (∑' n : ℕ, (α : ℝ≥0∞) ^ n) * U u α = ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) ∧
      ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) = U u α / (1 - (α : ℝ≥0∞)) := by sorry

end SennottDP.Tauberian
