-- Prove2me | Theorems.Thm_SDDiP_LagCut_eq_4_5
-- name    : SDDiP.LagCut.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:48:23.606744+00:00
-- url     : https://prove2.me/theorems/61b6ba9f-5f89-4bdb-873a-fa5fc2ce2eab
-- title:
--   (4.5) — the Lagrangian dual value equals the minimum over $\mathrm{conv}(X''_n) \cap \{z_n = \hat x\}$
-- statement:
--   Let $n$ be a node in iteration $i$ with the data of the node definition: $X_n$ nonempty, compact and mixed integer polyhedral, $f_n$ linear, the lower bound $L_n$ and the cuts of iterations $1,\dots,i$ forming $X''_n$, and the Lagrangian function $\mathcal L^i_n$ of (4.4). Assume $X''_n$ is nonempty. Let $\hat x \in \mathbb R^d$ be a parent state and let $\hat\pi$ be an optimal solution of the Lagrangian dual (4.3), i.e. $\mathcal L^i_n(\pi) + \pi^\top\hat x \le \mathcal L^i_n(\hat\pi) + \hat\pi^\top\hat x$ for every $\pi \in \mathbb R^d$. Then
--
--   $$\mathcal L^i_n(\hat\pi) + \hat\pi^\top \hat x = \min\big\{ f_n(x_n,y_n) + \theta_n : (z_n,x_n,y_n,\theta_n) \in \mathrm{conv}(X''_n),\ z_n = \hat x \big\},$$
--
--   and the minimum on the right is attained.
--
--   This is the strong duality of the Lagrangian relaxation of the copy constraint $z_n = \hat x$ (Geoffrion's theorem for this nodal problem); it is the first step of the proof of Theorem 3.
--
--   **Formalization Note** $\hat x$ is not required to be binary: the identity holds at every parent state at which the dual (4.3) has an optimal solution. The hypothesis that $X''_n$ (equivalently $X'_n$) is nonempty makes $\mathcal L^i_n$ a genuine minimum; the paper writes it as one. The minimum is stated as `IsLeast` of the set of values $f_n + \theta$ over points of `convexHull ℝ X''` with $z = \hat x$.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 479, (4.5)

import Mathlib
import Definitions.Def_SDDiP_LagCut_Node

namespace SDDiP.LagCut

open Node

/-- (4.5), Zou, Ahmed, Sun, Math. Program. 175 (2019), p. 479: if `π̂` is an optimal solution of the
Lagrangian dual (4.3) at the parent state `x̂`, then its value `𝓛^i_n(π̂) + π̂ᵀx̂` is the minimum of
`f_n(x, y) + θ` over `(z, x, y, θ) ∈ conv(X″_n)` with `z = x̂` (attained). `x̂` need not be binary;
`X″_n` is assumed nonempty, so that `𝓛^i_n` is a genuine minimum. -/
theorem eq_4_5 {d l : ℕ} (N : Node d l) (xhat : Fin d → ℝ) (hX' : N.X'.Nonempty)
    (πhat : Fin d → ℝ) (hopt : N.IsDualOptimal xhat πhat) :
    IsLeast {t | ∃ p ∈ convexHull ℝ N.X'', p.1 = xhat ∧ t = N.obj p}
      (N.lag πhat + πhat ⬝ᵥ xhat) := by sorry

end SDDiP.LagCut
