-- Prove2me | Theorems.Thm_RelSmoothFOM_DualAvg_eq_36
-- name    : RelSmoothFOM.DualAvg.eq_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:41.673591+00:00
-- url     : https://prove2.me/theorems/a66a6dc8-fb79-4c04-9ffa-d058c492793b
-- title:
--   (36), p. 348 — Σ_{i=0}^{k−1} a_{i+1} f(x^{i+1}) ≤ ψ*_k ≤ h(x) + A_k f(x)
-- statement:
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, let $f, h$ be convex on $Q$ and differentiable at every point of $Q$, and let $0 \le \mu < L$. Suppose $f$ is $L$-smooth and $\mu$-strongly convex relative to $h$ on $Q$, and let $(x^k)$ be a run of the dual averaging scheme (Algorithm 2) with models $\psi_k$ and $\psi^*_k = \psi_k(x^k)$. Then for every $k \ge 0$ and every $x \in Q$,
--   $$\sum_{i=0}^{k-1} a_{i+1} f(x^{i+1}) \le \psi^*_k \le h(x) + A_k f(x) .$$
--
--   Since the weights $a_{i+1}$ are positive, the left-hand side is at least $A_k \min_{1 \le i \le k} f(x^i)$; rearranging gives Theorem 3.2.
--
--   **Formalization Note** In the sum, $a_{i+1}$ multiplies $f(x^{i+1})$, as on the page.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 348, proof of Theorem 3.2, (36)

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

namespace RelSmoothFOM.DualAvg

/-- (36), proof of Theorem 3.2, p. 348: along a run of Algorithm 2, for every `k` and `u ∈ Q`,
`Σ_{i=0}^{k−1} a_{i+1} f(x^{i+1}) ≤ ψ*_k ≤ h(u) + A_k f(u)`. -/
theorem eq_36
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsDualAveragingRun Q f h L μ x) :
    ∀ k : ℕ, ∀ u ∈ Q,
      ∑ i ∈ Finset.range k, daWeight L μ i * f (x (i + 1)) ≤ daModel f h L μ x k (x k) ∧
      daModel f h L μ x k (x k) ≤ h u + daSum L μ k * f u := by sorry

end RelSmoothFOM.DualAvg
