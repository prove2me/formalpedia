-- Prove2me | Theorems.Thm_ProjLikeRetr_Stiefel_polar_unique
-- name    : ProjLikeRetr.Stiefel.polar_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:29:29.115976+00:00
-- url     : https://prove2.me/theorems/226ec17d-d62d-449a-b38a-c85c605b59e7
-- title:
--   §3.3, proof of Prop. 3.4, p. 10, citing [20, 7.3.2] — the polar form of a full-rank matrix is unique
-- statement:
--   Let $X\in\mathbb R^{n\times m}$ have full column rank, $\operatorname{rank}X=m$. Suppose
--
--   $$X=W_1P_1=W_2P_2,$$
--
--   where $W_1,W_2\in V_{n,m}$ have orthonormal columns and $P_1,P_2\in\mathbb R^{m\times m}$ are symmetric positive semidefinite. Then $W_1=W_2$ and $P_1=P_2$.
--
--   This is the uniqueness of the polar decomposition (Horn and Johnson, *Matrix Analysis*, Theorem 7.3.2, cited by the paper as [20, 7.3.2]). Proposition 3.4 uses it, with positive definite factors as a special case, to conclude that the nearest point of $V_{n,m}$ to $X$ is unique.
--
--   **Formalization Note** The statement allows positive *semidefinite* factors, as in the cited theorem; under the rank hypothesis any such factor is automatically positive definite, so the positive definite form of Proposition 3.4 is a special case.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 10, §3.3, proof of Proposition 3.4 (last sentence, citing [20, 7.3.2] = Horn & Johnson, Matrix Analysis, Thm 7.3.2)

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel

open scoped Matrix

namespace ProjLikeRetr.Stiefel

/-- §3.3, proof of Proposition 3.4, p. 10, citing [20, 7.3.2] (Horn–Johnson): the polar form of a
full-rank matrix is unique. If `X ∈ ℝ^{n×m}` has rank `m` and `X = W₁ P₁ = W₂ P₂` with
`W₁, W₂ ∈ V_{n,m}` and `P₁, P₂ ∈ ℝ^{m×m}` symmetric positive semidefinite, then `W₁ = W₂` and
`P₁ = P₂`. (Positive *definite* factors, as in Proposition 3.4, are a special case.) -/
theorem polar_unique {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (hrank : X.rank = m)
    (W₁ W₂ : Matrix (Fin n) (Fin m) ℝ) (P₁ P₂ : Matrix (Fin m) (Fin m) ℝ)
    (hW₁ : W₁ ∈ stiefel n m) (hW₂ : W₂ ∈ stiefel n m)
    (hP₁ : P₁.PosSemidef) (hP₂ : P₂.PosSemidef) (h₁ : X = W₁ * P₁) (h₂ : X = W₂ * P₂) :
    W₁ = W₂ ∧ P₁ = P₂ := by sorry

end ProjLikeRetr.Stiefel
