-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_mty_corrector_bullet
-- name    : SelfDualLP.Complexity.mty_corrector_bullet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:10.15999+00:00
-- url     : https://prove2.me/theorems/5deb05d9-3153-41a6-bc99-2210381e72c0
-- title:
--   Proof of Theorem 6, second bullet — the Mizuno–Todd–Ye corrector estimate
-- statement:
--   Let $\hat n\ge1$ and let $\hat x,\hat s,\hat d_x,\hat d_s\in\mathbb R^{\hat n}$ satisfy (14) with $\gamma=1$:
--   $$
--   \hat x>0,\quad \hat s>0,\quad \hat X\hat d_s+\hat S\hat d_x=-(\hat X\hat s-\hat\mu e),\quad \hat d_x^T\hat d_s=0,
--   $$
--   with $\hat\mu=\hat x^T\hat s/\hat n$, $\hat x(1)=\hat x+\hat d_x$, $\hat s(1)=\hat s+\hat d_s$ and $\hat\mu(1)=\hat x(1)^T\hat s(1)/\hat n$. If $\|\hat X\hat s-\hat\mu e\|\le\frac12\hat\mu$, then
--   $$
--   \hat x(1)>0,\quad \hat s(1)>0,\quad \|\hat X(1)\hat s(1)-\hat\mu(1)e\|\le\tfrac14\hat\mu(1),\quad \hat\mu(1)=\hat\mu .
--   $$
--
--   The corrector step returns the iterate to the narrower neighborhood without changing the gap.
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean norm; the equation of (14) is stated componentwise, with $\gamma=1$ written explicitly.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 62, proof of Theorem 6, second bullet (with (14) on p. 61)

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_Neighborhood

open Matrix

namespace SelfDualLP.Complexity

/-- Proof of Theorem 6, second bullet (p. 62), the Mizuno–Todd–Ye corrector estimate. Let
`n̂ ≥ 1` and let `x̂, ŝ, d̂_x, d̂_s ∈ ℝ^{n̂}` satisfy (14) with `γ = 1`: `x̂ > 0`, `ŝ > 0`,
`X̂d̂_s + Ŝd̂_x = −(X̂ŝ − μ̂e)`, `d̂_xᵀd̂_s = 0`, with `μ̂ = x̂ᵀŝ/n̂`. If
`‖X̂ŝ − μ̂e‖ ≤ (1/2)μ̂` then `x̂(1) = x̂ + d̂_x > 0`, `ŝ(1) = ŝ + d̂_s > 0`,
`‖X̂(1)ŝ(1) − μ̂(1)e‖ ≤ (1/4)μ̂(1)` and `μ̂(1) = μ̂`. -/
theorem mty_corrector_bullet {N : ℕ} (hN : 1 ≤ N) (x s dx ds : Fin N → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (hnewton : ∀ j, x j * ds j + s j * dx j = -(x j * s j - 1 * muHat x s))
    (horth : dx ⬝ᵥ ds = 0)
    (hcent : deviationHat x s ≤ (1 / 2) * muHat x s) :
    (∀ j, 0 < (x + dx) j) ∧ (∀ j, 0 < (s + ds) j) ∧
    deviationHat (x + dx) (s + ds) ≤ (1 / 4) * muHat (x + dx) (s + ds) ∧
    muHat (x + dx) (s + ds) = muHat x s := by sorry

end SelfDualLP.Complexity
