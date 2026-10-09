-- Prove2me | Theorems.Thm_ProjLikeRetr_Stiefel_projection_stiefel
-- name    : ProjLikeRetr.Stiefel.projection_stiefel
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:29:55.354984+00:00
-- url     : https://prove2.me/theorems/be1a43d2-2b3e-4a1b-a5ee-ac8743eefbb7
-- title:
--   Proposition 3.4, p. 10 — within σ_m(X̄) of V_{n,m}, the projection is unique and equals the polar factor Σ u_i v_iᵀ
-- statement:
--   Let $1\le m\le n$ and let $V_{n,m}=\{X\in\mathbb R^{n\times m}:X^\top X=I_m\}$ be the Stiefel manifold, with the Frobenius norm $\|X\|^2=\sum_{i,j}X_{ij}^2$ on $\mathbb R^{n\times m}$. Let $\bar X\in V_{n,m}$ and let $X\in\mathbb R^{n\times m}$ satisfy
--
--   $$\|X-\bar X\|<\sigma_m(\bar X),$$
--
--   where $\sigma_m$ is the $m$-th largest singular value (for $\bar X\in V_{n,m}$ its value is $1$). Let $X=U\Sigma V^\top$ be any singular value decomposition (3.5) of $X$, with $U=[u_1,\dots,u_n]$ and $V=[v_1,\dots,v_m]$. Then:
--
--   1. the projection of $X$ onto $V_{n,m}$ exists, is unique, and equals
--   $$P_{V_{n,m}}(X)=\sum_{i=1}^m u_iv_i^\top;$$
--   that is, $\sum_{i=1}^m u_iv_i^\top$ belongs to $V_{n,m}$, satisfies $\|X-\sum_i u_iv_i^\top\|\le\|X-Y\|$ for all $Y\in V_{n,m}$, and is the only point of $V_{n,m}$ with this property;
--   2. it is the factor $W$ of the polar decomposition $X=WS$: whenever $X=WP$ with $W\in V_{n,m}$ and $P\in\mathbb R^{m\times m}$ symmetric positive definite, $W=\sum_{i=1}^m u_iv_i^\top$; and such a decomposition $X=\big(\sum_{i=1}^m u_iv_i^\top\big)P$ with $P$ symmetric positive definite exists.
--
--   By Proposition 3.2 of the paper, the projection therefore gives a retraction on the Stiefel manifold that is computed from one singular value decomposition.
--
--   **Formalization Note** The page prints the projection as $P_{\mathcal R_r}(X)$, a misprint carried over from Proposition 3.3; the proposition is about $P_{V_{n,m}}(X)$, as its first sentence says. The projection is the set of nearest points (`IsMetricProjection (stiefel n m) X`), and "exists and is unique" is the equality of that set with the singleton. $\sum_{i=1}^m u_iv_i^\top$ is `frameOfSVD U V` $=UEV^\top$ with $E$ the $n\times m$ rectangular identity. The radius $\sigma_m(\bar X)$ is kept as `sv Xbar m`, strict. The hypothesis $0<m$ excludes the empty frame; $m\le n$ is the page's assumption of §3.3. The conclusion holds for every singular value decomposition supplied. The existence clause in item 2 makes "it is the $W$ of the polar decomposition" two-sided.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 10, §3.3, Proposition 3.4 (the display's P_{R_r}(X) is a misprint for P_{V_{n,m}}(X))

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ProjLikeRetr_Stiefel_SVD

open RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius

namespace ProjLikeRetr.Stiefel

/-- Proposition 3.4 (Projection onto Stiefel manifolds), p. 10. Let `1 ≤ m ≤ n` and
`X̄ ∈ V_{n,m}` (`Xbar`). For any `X ∈ ℝ^{n×m}` with `‖X − X̄‖ < σ_m(X̄)` (Frobenius norm,
strict) and any singular value decomposition `X = U Σ Vᵀ` (3.5) of `X`:
1. the projection of `X` onto `V_{n,m}` exists, is unique, and equals
   `Σ_{i=1}^m u_i v_iᵀ = U E Vᵀ` (`frameOfSVD U V`): the set of nearest points of `V_{n,m}` to
   `X` is exactly `{U E Vᵀ}`;
2. it is the `W` of the polar decomposition `X = W S`: every factorization `X = W P` with
   `W ∈ V_{n,m}` and `P ∈ ℝ^{m×m}` symmetric positive definite has `W = U E Vᵀ`, and such a
   factorization with `W = U E Vᵀ` exists.
The page prints the projection as `P_{ℛ_r}(X)`, a misprint for `P_{V_{n,m}}(X)`. -/
theorem projection_stiefel {n m : ℕ} (hmn : m ≤ n) (hm : 0 < m)
    (Xbar X : Matrix (Fin n) (Fin m) ℝ) (hXbar : Xbar ∈ stiefel n m)
    (hX : ‖X - Xbar‖ < ProjLikeRetr.FixedRank.sv Xbar m)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : ProjLikeRetr.FixedRank.IsSVD X U S V) :
    {Y | IsMetricProjection (stiefel n m) X Y} = {frameOfSVD U V} ∧
      (∀ (W : Matrix (Fin n) (Fin m) ℝ) (P : Matrix (Fin m) (Fin m) ℝ),
        W ∈ stiefel n m → P.PosDef → X = W * P → W = frameOfSVD U V) ∧
      ∃ P : Matrix (Fin m) (Fin m) ℝ, P.PosDef ∧ X = frameOfSVD U V * P := by sorry

end ProjLikeRetr.Stiefel
