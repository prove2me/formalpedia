-- Prove2me | Theorems.Thm_ProjLikeRetr_Stiefel_trace_bound_stiefel
-- name    : ProjLikeRetr.Stiefel.trace_bound_stiefel
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:29:46.404976+00:00
-- url     : https://prove2.me/theorems/9ed9c518-8349-4c52-b04a-78eabea4440a
-- title:
--   §3.3, proof of Prop. 3.4, p. 10 — max_{Y∈V_{n,m}} trace(YᵀX) = Σ_{i=1}^m σ_i, attained at Y = UVᵀ
-- statement:
--   Let $m\le n$ and let $X=U\Sigma V^\top$ be a singular value decomposition (3.5) of $X\in\mathbb R^{n\times m}$, with diagonal entries $\sigma_i=\Sigma_{ii}$, $i=1,\dots,m$. Then
--
--   1. for every $Y$ in the Stiefel manifold $V_{n,m}$,
--   $$\operatorname{trace}(Y^\top X)\le\sum_{i=1}^m\sigma_i;$$
--   2. the matrix $\sum_{i=1}^m u_iv_i^\top=UEV^\top$ (written $UV^\top$ on the page; $E$ is the $n\times m$ rectangular identity) lies in $V_{n,m}$ and attains the bound:
--   $$\operatorname{trace}\big((UEV^\top)^\top X\big)=\sum_{i=1}^m\sigma_i.$$
--
--   Together with the identity $\|X-Y\|^2=\|X\|^2+m-2\operatorname{trace}(Y^\top X)$ on $V_{n,m}$, this shows that $UEV^\top$ is a nearest point of $V_{n,m}$ to $X$; it holds for every $X$ and every singular value decomposition, with no condition on the singular values.
--
--   **Formalization Note** For a 0-based column index $i<m$, the diagonal entry $\sigma_{i+1}$ is `S (Fin.castLE hmn i) i`, which needs $m\le n$. `frameOfSVD U V` is $UEV^\top$.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 10, §3.3, proof of Proposition 3.4 (display of max_{Y∈V_{n,m}} trace(YᵀX) and the two sentences after it)

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ProjLikeRetr_Stiefel_SVD

open scoped Matrix

namespace ProjLikeRetr.Stiefel

/-- §3.3, proof of Proposition 3.4, p. 10: let `m ≤ n` and let `X = U Σ Vᵀ` be a singular value
decomposition (3.5) of `X ∈ ℝ^{n×m}` (`Σ` is `S`, with diagonal entries `σ_i = S_{ii}`). Then
`trace(YᵀX) ≤ Σ_{i=1}^m σ_i` for every `Y ∈ V_{n,m}`, and the bound is attained by
`Y = U E Vᵀ = Σ_{i=1}^m u_i v_iᵀ` (the page's `U Vᵀ`), which lies in `V_{n,m}`. The diagonal
entry `σ_{i+1}` (0-based `i : Fin m`) is `S (Fin.castLE hmn i) i`. -/
theorem trace_bound_stiefel {n m : ℕ} (hmn : m ≤ n) (X : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : ProjLikeRetr.FixedRank.IsSVD X U S V) :
    (∀ Y ∈ stiefel n m, (Yᵀ * X).trace ≤ ∑ i : Fin m, S (Fin.castLE hmn i) i) ∧
      frameOfSVD U V ∈ stiefel n m ∧
      ((frameOfSVD U V)ᵀ * X).trace = ∑ i : Fin m, S (Fin.castLE hmn i) i := by sorry

end ProjLikeRetr.Stiefel
