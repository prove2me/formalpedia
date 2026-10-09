-- Prove2me | Theorems.Thm_RelSmoothFOM_DualAvg_eq_34
-- name    : RelSmoothFOM.DualAvg.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:43.249935+00:00
-- url     : https://prove2.me/theorems/89e5b15e-b213-417f-badd-9dc77cd70fee
-- title:
--   (34), p. 347 — along the dual averaging scheme, ψ*_k ≤ h(x) + A_k f(x) for every x ∈ Q
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, and let $f, h$ be convex on $Q$ and differentiable at every point of $Q$. Let $0 \le \mu < L$ and suppose $f$ is $\mu$-strongly convex relative to $h$ on $Q$. Let $(x^k)$ be a run of the dual averaging scheme (Algorithm 2), with models $\psi_k$ and $\psi^*_k = \psi_k(x^k)$. Then for every $k \ge 0$ and every $x \in Q$,
--   $$\psi^*_k \le h(x) + A_k f(x), \qquad A_k = \sum_{i=0}^{k-1} a_{i+1}.$$
--
--   This is the upper half of (36): the model's optimal value never exceeds $h$ plus $A_k$ times the objective at any feasible point.
--
--   **Formalization Note** For $k \ge 1$, $\psi^*_k = \psi_k(x^k)$ because $x^k$ minimises $\psi_k$ over $Q$; for $k = 0$, $\psi_0 = h$ and $x^0$ is the $h$-center. The relative smoothness condition is not needed and is not assumed.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 347, proof of Theorem 3.2, (34)

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

namespace RelSmoothFOM.DualAvg

/-- (34), proof of Theorem 3.2, p. 347: along a run of Algorithm 2, for every `k` and every
`u ∈ Q`, `ψ*_k = ψ_k(x^k) ≤ h(u) + A_k f(u)`. -/
theorem eq_34
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsDualAveragingRun Q f h L μ x) :
    ∀ k : ℕ, ∀ u ∈ Q, daModel f h L μ x k (x k) ≤ h u + daSum L μ k * f u := by sorry

end RelSmoothFOM.DualAvg
