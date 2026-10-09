-- Prove2me | Theorems.Thm_RelSmoothFOM_DualAvg_eq_35
-- name    : RelSmoothFOM.DualAvg.eq_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:31.762219+00:00
-- url     : https://prove2.me/theorems/e7d620ae-71bc-4f51-88bb-357ed5e27ad9
-- title:
--   (35), p. 347 — (1 + μA_k)D_h(x, x^k) = D_{ψ_k}(x, x^k) ≤ ψ_k(x) − ψ*_k
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, let $f, h$ be convex on $Q$ and differentiable at every point of $Q$, and let $0 \le \mu < L$. Let $(x^k)$ be a run of the dual averaging scheme (Algorithm 2) with models $\psi_k$ and $\psi^*_k = \psi_k(x^k)$. Then for every $k \ge 0$ and every $x \in Q$,
--   $$(1 + \mu A_k)\, D_h(x, x^k) = D_{\psi_k}(x, x^k) \le \psi_k(x) - \psi^*_k .$$
--
--   The equality holds because $\psi_k$ is an affine function plus $(1 + \mu A_k) h$, so the two have the same Bregman distance; the inequality is the first-order optimality condition of $x^k$ for $\psi_k$ over $Q$. It is the step that turns the minimisation in Algorithm 2 into the growth estimate for $\psi^*_{k+1}$.
--
--   **Formalization Note** $D_{\psi_k}$ is the Bregman distance (7) of the function $\psi_k$, with its Fréchet derivative at $x^k \in Q$; $\psi_k$ is differentiable there because $h$ is. No relative smoothness or relative strong convexity is assumed: neither is used.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 347, proof of Theorem 3.2, (35)

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

namespace RelSmoothFOM.DualAvg

/-- (35), proof of Theorem 3.2, p. 347: along a run of Algorithm 2, for every `k` and `u ∈ Q`,
`(1 + μA_k) D_h(u, x^k) = D_{ψ_k}(u, x^k) ≤ ψ_k(u) − ψ*_k`, where `ψ_k = daModel f h L μ x k`
and `ψ*_k = ψ_k(x^k)`. -/
theorem eq_35
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L)
    (x : ℕ → E) (hrun : IsDualAveragingRun Q f h L μ x) :
    ∀ k : ℕ, ∀ u ∈ Q,
      (1 + μ * daSum L μ k) * bregman h u (x k) = bregman (daModel f h L μ x k) u (x k) ∧
      bregman (daModel f h L μ x k) u (x k) ≤
        daModel f h L μ x k u - daModel f h L μ x k (x k) := by sorry

end RelSmoothFOM.DualAvg
