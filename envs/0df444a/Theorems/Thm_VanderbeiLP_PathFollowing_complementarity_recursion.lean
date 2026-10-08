-- Prove2me | Theorems.Thm_VanderbeiLP_PathFollowing_complementarity_recursion
-- name    : VanderbeiLP.PathFollowing.complementarity_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T20:04:29.641454+00:00
-- url     : https://prove2.me/theorems/c32d94c0-348c-428c-b709-764f95b9fc8d
-- title:
--   Eq. (18.11) — $\gamma^{(k)} \le (1-\tilde t)\gamma^{(k-1)} + \tilde M(1-t)^{k-1}$
-- statement:
--   Let $0 < \delta < 1$ and $0 < r < 1$, and let $(x^{(k)}, w^{(k)}, y^{(k)}, z^{(k)})$, $k = 0, 1, \dots, K + 1$, be iterates of the path-following method (Fig. 18.1 with step length (18.7)): for each $k \le K$ the point with index $k+1$ is obtained from the point with index $k$ by one iteration using some solution $(\Delta x^{(k)}, \dots, \Delta z^{(k)})$ of the Newton system, with step length $\theta^{(k)}$. Write $\rho^{(k)}$, $\sigma^{(k)}$, $\gamma^{(k)}$ for the primal infeasibility, dual infeasibility and complementarity of the $k$-th iterate. Suppose there are real numbers $t > 0$ and $M$ such that for all $k \le K$
--
--   $$\theta^{(k)} \ge t, \qquad \|x^{(k)}\|_\infty \le M, \qquad \|y^{(k)}\|_\infty \le M.$$
--
--   Then for every $k$ with $1 \le k \le K$,
--
--   $$\gamma^{(k)} \le (1 - t(1 - \delta))\gamma^{(k-1)} + M(1 - t)^{k-1}\left(\|\rho^{(0)}\|_1 + \|\sigma^{(0)}\|_1\right).$$
--
--   This recursion, derived from Eqs. (18.8)–(18.10), is the core of the proof of Theorem 18.1; unrolling it gives the geometric decay of the complementarity.
--
--   **Formalization Note** The Lean statement is indexed by $k + 1$ instead of $k$ (for $k + 1 \le K$), which avoids natural-number subtraction; $\theta^{(k)}$ is the step length computed at the $k$-th iterate, the one used to move to iterate $k+1$. The hypotheses are those of Theorem 18.1, with the same index range $k \le K$.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 278, Eq. (18.11), in the proof of Theorem 18.1 (PDF p. 288)

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod

open Matrix

namespace VanderbeiLP.PathFollowing

/-- Vanderbei, p. 278, Eq. (18.11), in the setting of Theorem 18.1: for every `k` with
`k + 1 ≤ K`,
`γ⁽ᵏ⁺¹⁾ ≤ (1 − t(1 − δ)) γ⁽ᵏ⁾ + M (1 − t)ᵏ (‖ρ⁽⁰⁾‖₁ + ‖σ⁽⁰⁾‖₁)`
(the book's (18.11) with its index `k` shifted to `k + 1`). Here `s k` is the `k`-th iterate,
`d k` the direction computed at it and `θ⁽ᵏ⁾ = stepLength r (s k) (d k)`. -/
theorem complementarity_recursion {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (t M : ℝ) (K : ℕ) (ht : 0 < t)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k))
    (hx : ∀ k ≤ K, normInf (s k).x ≤ M) (hy : ∀ k ≤ K, normInf (s k).y ≤ M) :
    ∀ k, k + 1 ≤ K →
      complementarity (s (k + 1)) ≤
        (1 - t * (1 - δ)) * complementarity (s k)
          + M * (1 - t) ^ k
            * (norm1 (primalInfeas A b (s 0)) + norm1 (dualInfeas A c (s 0))) := by sorry

end VanderbeiLP.PathFollowing
