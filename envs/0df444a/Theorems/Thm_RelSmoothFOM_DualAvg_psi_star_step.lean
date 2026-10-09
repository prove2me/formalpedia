-- Prove2me | Theorems.Thm_RelSmoothFOM_DualAvg_psi_star_step
-- name    : RelSmoothFOM.DualAvg.psi_star_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:58.137627+00:00
-- url     : https://prove2.me/theorems/cbdf9f11-ef4d-45e8-a0f6-cb66d0feb6a0
-- title:
--   Proof of Theorem 3.2, pp. 347–348 — ψ*_{k+1} ≥ ψ*_k + a_{k+1} f(x^{k+1})
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, let $f, h$ be convex on $Q$ and differentiable at every point of $Q$, and let $0 \le \mu < L$. Suppose $f$ is $L$-smooth relative to $h$ on $Q$, and let $(x^k)$ be a run of the dual averaging scheme (Algorithm 2) with models $\psi_k$ and $\psi^*_k = \psi_k(x^k)$. Then for every $k \ge 0$,
--   $$\psi^*_{k+1} \ge \psi^*_k + a_{k+1} f(x^{k+1}) .$$
--
--   Summed over $k$, this recursion gives the lower half of (36), $\sum_{i=0}^{k-1} a_{i+1} f(x^{i+1}) \le \psi^*_k$.
--
--   **Formalization Note** Relative strong convexity is not needed and is not assumed.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), pp. 347–348, proof of Theorem 3.2, display preceding (36)

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

namespace RelSmoothFOM.DualAvg

/-- Proof of Theorem 3.2, pp. 347–348: along a run of Algorithm 2, for every `k`,
`ψ*_{k+1} ≥ ψ*_k + a_{k+1} f(x^{k+1})`, where `ψ*_k = ψ_k(x^k)`. -/
theorem psi_star_step
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L)
    (x : ℕ → E) (hrun : IsDualAveragingRun Q f h L μ x) :
    ∀ k : ℕ, daModel f h L μ x (k + 1) (x (k + 1)) ≥
      daModel f h L μ x k (x k) + daWeight L μ k * f (x (k + 1)) := by sorry

end RelSmoothFOM.DualAvg
