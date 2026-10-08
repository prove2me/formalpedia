-- Prove2me | Theorems.Thm_VanderbeiLP_PathFollowing_path_following_convergence
-- name    : VanderbeiLP.PathFollowing.path_following_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T20:11:06.192847+00:00
-- url     : https://prove2.me/theorems/220d8944-f802-44d2-966d-fe70c0b837f8
-- title:
--   Theorem 18.1 — geometric decay of infeasibility and complementarity along the path-following iterates
-- statement:
--   Let $0 < \delta < 1$ and $0 < r < 1$, and let $(x^{(k)}, w^{(k)}, y^{(k)}, z^{(k)})$, $k = 0, 1, \dots, K + 1$, be iterates of the path-following method (Fig. 18.1 with step length (18.7)) started from a strictly positive point: for each $k \le K$ the point with index $k+1$ is obtained from the point with index $k$ by one iteration, using some solution of the Newton system (18.1)–(18.4) with $\mu = \delta\gamma^{(k)}/(n+m)$, with step length $\theta^{(k)}$. Write $\rho^{(k)} = b - Ax^{(k)} - w^{(k)}$, $\sigma^{(k)} = c - A^Ty^{(k)} + z^{(k)}$ and $\gamma^{(k)} = z^{(k)T}x^{(k)} + y^{(k)T}w^{(k)}$.
--
--   Suppose there are a real number $t > 0$, a real number $M$ and an integer $K \ge 0$ such that for all $k \le K$
--
--   $$\theta^{(k)} \ge t, \qquad \|x^{(k)}\|_\infty \le M, \qquad \|y^{(k)}\|_\infty \le M.$$
--
--   Then, with $\tilde t = t(1 - \delta)$ and
--
--   $$\bar M = \gamma^{(0)} + \frac{M\left(\|\rho^{(0)}\|_1 + \|\sigma^{(0)}\|_1\right)}{\delta t},$$
--
--   for all $k \le K$
--
--   $$\|\rho^{(k)}\|_1 \le (1 - t)^k\|\rho^{(0)}\|_1, \qquad \|\sigma^{(k)}\|_1 \le (1 - t)^k\|\sigma^{(0)}\|_1, \qquad \gamma^{(k)} \le (1 - \tilde t)^k\bar M.$$
--
--   So as long as the step lengths stay bounded away from zero and the iterates stay bounded, the primal and dual infeasibilities decrease geometrically at rate $1 - t$ and the complementarity at the slower rate $1 - \tilde t$. The result is conditional: it does not show that the step lengths remain bounded below.
--
--   **Formalization Note** The book states "there exists a constant $\bar M < \infty$". Since $K$ is fixed, that existential alone would be satisfied trivially by the finitely many values $\gamma^{(k)}/(1-\tilde t)^k$; the book's proof yields the explicit constant $\bar M = \gamma^{(0)} + M(\|\rho^{(0)}\|_1 + \|\sigma^{(0)}\|_1)/(\delta t)$, which does not depend on $K$, and this constant is stated. The step length $\theta^{(k)}$ is the one computed at the $k$-th iterate; as in the book, the hypotheses range over all $k \le K$, so the iteration from index $K$ to $K+1$ is part of the data. Strict positivity of every iterate is part of the definition of an iteration (it follows from positivity of the starting point).
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, pp. 277–279, Theorem 18.1 and its proof (PDF pp. 287–289); constant M̄ from the last display of the proof, p. 279 (PDF p. 289)

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod

open Matrix

namespace VanderbeiLP.PathFollowing

/-- Vanderbei, Theorem 18.1 (pp. 277–279). Along the iterates `s 0, s 1, …` of the
path-following method (Fig. 18.1 with step length (18.7)), if `θ⁽ᵏ⁾ ≥ t > 0`,
`‖x⁽ᵏ⁾‖∞ ≤ M` and `‖y⁽ᵏ⁾‖∞ ≤ M` for all `k ≤ K`, then for all `k ≤ K`
`‖ρ⁽ᵏ⁾‖₁ ≤ (1 − t)ᵏ‖ρ⁽⁰⁾‖₁`, `‖σ⁽ᵏ⁾‖₁ ≤ (1 − t)ᵏ‖σ⁽⁰⁾‖₁` and `γ⁽ᵏ⁾ ≤ (1 − t̃)ᵏ M̄` with
`t̃ = t(1 − δ)`. The book writes "there exists `M̄ < ∞`"; its proof yields
`M̄ = γ⁽⁰⁾ + M(‖ρ⁽⁰⁾‖₁ + ‖σ⁽⁰⁾‖₁)/(δt)`, which is the constant stated here. -/
theorem path_following_convergence {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (t M : ℝ) (K : ℕ) (ht : 0 < t)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k))
    (hx : ∀ k ≤ K, normInf (s k).x ≤ M) (hy : ∀ k ≤ K, normInf (s k).y ≤ M) :
    ∀ k ≤ K,
      norm1 (primalInfeas A b (s k)) ≤ (1 - t) ^ k * norm1 (primalInfeas A b (s 0)) ∧
      norm1 (dualInfeas A c (s k)) ≤ (1 - t) ^ k * norm1 (dualInfeas A c (s 0)) ∧
      complementarity (s k) ≤
        (1 - t * (1 - δ)) ^ k
          * (complementarity (s 0)
              + M * (norm1 (primalInfeas A b (s 0)) + norm1 (dualInfeas A c (s 0)))
                / (δ * t)) := by sorry

end VanderbeiLP.PathFollowing
