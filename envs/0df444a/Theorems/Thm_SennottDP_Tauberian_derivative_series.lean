-- Prove2me | Theorems.Thm_SennottDP_Tauberian_derivative_series
-- name    : SennottDP.Tauberian.derivative_series
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:04:02.30857+00:00
-- url     : https://prove2.me/theorems/63ac2000-5c5f-4e7c-b167-7b6c04139400
-- title:
--   Remark A.3.1 — a power series is differentiable inside its radius, and the derived series has the same radius
-- statement:
--   Let $(u_n)$ be finite nonnegative terms whose power series $U(\alpha) = \sum_n \alpha^n u_n$ has radius of convergence $R > 0$. Then $U$ is differentiable at every $\alpha \in (0, R)$, with derivative given by term-by-term differentiation,
--   $$\frac{dU(\alpha)}{d\alpha} = \sum_{n=1}^{\infty} n\alpha^{n-1} u_n,$$
--   and the power series on the right, whose $m$-th coefficient is $(m+1)u_{m+1}$, again has radius of convergence $R$.
--
--   Since the radius does not change, the procedure can be repeated to obtain derivatives of every order.
--
--   **Formalization Note** The terms are taken in $\mathbb{R}_{\ge 0}$ (finite): the book's discussion of the radius of convergence tacitly assumes finite terms, since a single infinite term makes $U(\alpha) = \infty$ for every $\alpha > 0$ without changing the $\limsup$. $U$ is the real sum $\sum_n x^n u_n$; the $n = 0$ term of the derivative series is $0$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 279, Remark A.3.1, (A.21)–(A.22)

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 279, Remark A.3.1: let `u_n` be finite nonnegative terms whose power series
has radius of convergence `R > 0`. Then `U(α) = ∑ α^n u_n` is differentiable at every
`α ∈ (0, R)` with derivative the term-by-term derivative (A.22) `∑_{n ≥ 1} n α^{n-1} u_n`, and the
power series (A.22), whose `m`-th coefficient is `(m + 1) u_{m+1}`, again has radius of
convergence `R`. -/
theorem derivative_series (u : ℕ → ℝ≥0) (hR : 0 < radius (fun n => (u n : ℝ≥0∞))) :
    (∀ α : ℝ, 0 < α → ENNReal.ofReal α < radius (fun n => (u n : ℝ≥0∞)) →
        HasDerivAt (fun x : ℝ => ∑' n : ℕ, x ^ n * (u n : ℝ))
          (∑' n : ℕ, (n : ℝ) * α ^ (n - 1) * (u n : ℝ)) α) ∧
      radius (fun m => ((m + 1 : ℕ) : ℝ≥0∞) * (u (m + 1) : ℝ≥0∞))
        = radius (fun n => (u n : ℝ≥0∞)) := by sorry

end SennottDP.Tauberian
