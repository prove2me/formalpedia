-- Prove2me | Theorems.Thm_RobinsonSR_Schur_inclusion_iff_schur
-- name    : RobinsonSR.Schur.inclusion_iff_schur
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:17.898578+00:00
-- url     : https://prove2.me/theorems/db8527ac-7b1d-4961-8b08-646a41845bf6
-- title:
--   Block inclusion (3.5) is equivalent to (3.6) and (3.7)
-- statement:
--   Suppose $A_{11}$ is nonsingular and write $y=(y_1,y_2)$ and $w=(w_1,w_2)$. For any set $K\subseteq\mathbb R^s$, the inclusion $y\in Aw+N_{\mathbb R^r\times K}(w)$ holds exactly when
--
--   $$
--   w_1=A_{11}^{-1}y_1-A_{11}^{-1}A_{12}w_2,
--   \qquad
--   y_2-A_{21}A_{11}^{-1}y_1\in(A/A_{11})w_2+N_K(w_2).
--   $$
--
--   This is the paper's algebraic reduction from the block generalized equation to one involving its Schur complement. No convexity or closedness of $K$ is needed for the equivalence.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 51, proof of Theorem 3.1, (3.5)–(3.7)

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, p. 51, equations (3.5)-(3.7). -/
theorem inclusion_iff_schur (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (hA₁₁ : A₁₁.det ≠ 0) (K : Set (EuclideanSpace ℝ (Fin s)))
    (y w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    (y - (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin w ∈
      normalCone (prodSet K) w) ↔
    (upperBlock w = (A₁₁⁻¹).toEuclideanLin (upperBlock y) -
      (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (lowerBlock w))) ∧
    (lowerBlock y - A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (upperBlock y)) -
      (schur A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin (lowerBlock w) ∈
      normalCone K (lowerBlock w)) := by sorry

end RobinsonSR.Schur
