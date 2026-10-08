-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_mty_predictor_bullet
-- name    : SelfDualLP.Complexity.mty_predictor_bullet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:14.734045+00:00
-- url     : https://prove2.me/theorems/d4428338-ea9c-457c-b0a5-c3d833756588
-- title:
--   Proof of Theorem 6, first bullet — the Mizuno–Todd–Ye predictor estimate for $\alpha\in[0,8^{-1/4}/\sqrt{\hat n}]$
-- statement:
--   Let $\hat n\ge1$ and let $\hat x,\hat s,\hat d_x,\hat d_s\in\mathbb R^{\hat n}$ satisfy (14) with $\gamma=0$:
--   $$
--   \hat x>0,\quad \hat s>0,\quad \hat X\hat d_s+\hat S\hat d_x=-\hat X\hat s,\quad \hat d_x^T\hat d_s=0,
--   $$
--   where $\hat X=\operatorname{diag}(\hat x)$, $\hat S=\operatorname{diag}(\hat s)$. Put $\hat\mu=\hat x^T\hat s/\hat n$, $\hat x(\alpha)=\hat x+\alpha\hat d_x$, $\hat s(\alpha)=\hat s+\alpha\hat d_s$ and $\hat\mu(\alpha)=\hat x(\alpha)^T\hat s(\alpha)/\hat n$. If $\|\hat X\hat s-\hat\mu e\|\le\frac14\hat\mu$, then for every $\alpha\in[0,\,8^{-1/4}/\sqrt{\hat n}]$:
--   $$
--   \hat x(\alpha)>0,\quad \hat s(\alpha)>0,\quad \|\hat X(\alpha)\hat s(\alpha)-\hat\mu(\alpha)e\|\le\tfrac12\hat\mu(\alpha),\quad \hat\mu(\alpha)=(1-\alpha)\hat\mu .
--   $$
--
--   This is the step-length estimate that yields the factor $1-8^{-1/4}/\sqrt{n+1}$ per predictor step.
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean norm, written out as a square root of a sum of squares; the exponent $8^{-.25}$ of the paper is $8^{-1/4}$ (real power). The equation of (14) is stated componentwise, with $\gamma=0$ written explicitly.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 62, proof of Theorem 6, first bullet (with (14) on p. 61)

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_Neighborhood

open Matrix

namespace SelfDualLP.Complexity

/-- Proof of Theorem 6, first bullet (p. 62), the Mizuno–Todd–Ye predictor estimate. Let
`n̂ ≥ 1` and let `x̂, ŝ, d̂_x, d̂_s ∈ ℝ^{n̂}` satisfy (14) with `γ = 0`: `x̂ > 0`, `ŝ > 0`,
`X̂d̂_s + Ŝd̂_x = −X̂ŝ`, `d̂_xᵀd̂_s = 0`. Write `μ̂ = x̂ᵀŝ/n̂`, `x̂(α) = x̂ + αd̂_x`,
`ŝ(α) = ŝ + αd̂_s`, `μ̂(α) = x̂(α)ᵀŝ(α)/n̂`. If `‖X̂ŝ − μ̂e‖ ≤ (1/4)μ̂` then for every
`α ∈ [0, 8^{−1/4}/√n̂]`: `x̂(α) > 0`, `ŝ(α) > 0`, `‖X̂(α)ŝ(α) − μ̂(α)e‖ ≤ (1/2)μ̂(α)` and
`μ̂(α) = (1 − α)μ̂`. -/
theorem mty_predictor_bullet {N : ℕ} (hN : 1 ≤ N) (x s dx ds : Fin N → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (hnewton : ∀ j, x j * ds j + s j * dx j = -(x j * s j - 0 * muHat x s))
    (horth : dx ⬝ᵥ ds = 0)
    (hcent : deviationHat x s ≤ (1 / 4) * muHat x s) :
    ∀ α : ℝ, 0 ≤ α → α ≤ (8 : ℝ) ^ (-(1 / 4 : ℝ)) / Real.sqrt N →
      (∀ j, 0 < (x + α • dx) j) ∧ (∀ j, 0 < (s + α • ds) j) ∧
      deviationHat (x + α • dx) (s + α • ds) ≤ (1 / 2) * muHat (x + α • dx) (s + α • ds) ∧
      muHat (x + α • dx) (s + α • ds) = (1 - α) * muHat x s := by sorry

end SelfDualLP.Complexity
