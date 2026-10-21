-- Prove2me | Theorems.Thm_StochSQP_Vanishing_theorem_3
-- name    : StochSQP.Vanishing.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:52.436784+00:00
-- url     : https://prove2.me/theorems/d32391a6-363b-44d7-afc4-854e0a937ee0
-- title:
--   Theorem 3, p. 21 — if the merit parameter vanishes with bounded gradient error, liminf ‖J_kᵀc_k‖₂ = 0
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ and $c : \mathbb R^n \to \mathbb R^m$ define the problem $\min f(x)$ s.t. $c(x) = 0$, and consider a run of the stochastic SQP algorithm (Algorithm 1) with valid parameters, under Assumption 1 (on an open convex set $X$ containing all iterates) and Assumption 3. Suppose that Assumption 5 holds in this run, i.e. the merit parameters vanish, $\tau_k \to 0$, and the stochastic gradients satisfy $\|g_k - \nabla f(x_k)\|_2^2 \le M$ for all $k$ with $M > 0$. Suppose that $\{\beta_k\}$ satisfies (28) for all $k$, and either
--
--   (a) $\beta_k = \beta \in (0,1)$ for all $k$, or
--
--   (b) $\sum_{k=0}^\infty \beta_k = \infty$, $\sum_{k=0}^\infty \beta_k^2 < \infty$, and either $|\{k \in \mathbb N : \|u_k\|_2^2 < \chi_k\|v_k\|_2^2\}| = \infty$ or $\sum_{k=0}^\infty \beta_k\tau_k = \infty$.
--
--   Then
--   $$\liminf_{k \to \infty} \|J_k^T c_k\|_2 = 0 .$$
--
--   If the merit parameter vanishes while the gradient errors stay bounded, a subsequence of iterates approaches stationarity for the constraint violation measure $\tfrac12\|c(x)\|_2^2$; this is the guarantee the algorithm provides when the constraint Jacobians tend to rank deficiency.
--
--   **Formalization Note.** Since $\|J_k^T c_k\|_2 \ge 0$, $\liminf = 0$ is stated as: for every $\gamma > 0$ there are infinitely many $k$ with $\|J_k^T c_k\|_2 < \gamma$ (`∃ᶠ k in atTop`), which avoids `Filter.liminf` on unbounded real sequences. $\sum\beta_k = \infty$ is `¬ Summable β` (the terms are positive) and $\sum\beta_k\tau_k = \infty$ is `¬ Summable (β·τ)`. Assumption 5 is read pathwise; its unbiasedness clause $\mathbb E_{k,\tau,\rm zero}[g_k] = \nabla f(x_k)$ is dropped, Assumption 3's "chosen independently from $g_k$" is dropped, and $f$'s expectation structure is not modelled (see the definitions file).
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 21, Theorem 3 (Assumption 5, p. 19)

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem theorem_3 {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (M : ℝ) (hM : 0 < M) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ^ 2 ≤ M)
    (hτ : Filter.Tendsto R.τ Filter.atTop (nhds 0))
    (h28 : Cond28 A R)
    (hab : (∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ k, R.β k = β) ∨
      (¬ Summable R.β ∧ Summable (fun k => R.β k ^ 2) ∧
        ({k : ℕ | ‖R.u k‖ ^ 2 < R.χ k * ‖R.v k‖ ^ 2}.Infinite ∨
          ¬ Summable (fun k => R.β k * R.τ k)))) :
    ∀ γ > (0 : ℝ), ∃ᶠ k in Filter.atTop, ‖P.Jt (R.x k) (P.c (R.x k))‖ < γ := by sorry

end StochSQP.Vanishing
