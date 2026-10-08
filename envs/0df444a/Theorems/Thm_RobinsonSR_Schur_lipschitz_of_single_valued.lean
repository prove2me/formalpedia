-- Prove2me | Theorems.Thm_RobinsonSR_Schur_lipschitz_of_single_valued
-- name    : RobinsonSR.Schur.lipschitz_of_single_valued
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:06:14.633206+00:00
-- url     : https://prove2.me/theorems/07bf3c97-ec5c-45a2-8102-57bd671897c2
-- title:
--   A single-valued polyhedral inverse is Lipschitz on a convex set
-- statement:
--   For polyhedral $K$ and $T(w)=Aw+N_{\mathbb R^r\times K}(w)$, one fixed modulus $\lambda\geq0$ gives the local upper Lipschitz estimate at every point. If $D\subseteq\mathbb R^{r+s}$ is convex and $T^{-1}(y)$ is a singleton for each $y\in D$, then
--
--   $$
--   \|T^{-1}(y_1)-T^{-1}(y_2)\|\leq\lambda\|y_1-y_2\|
--   \qquad(y_1,y_2\in D).
--   $$
--
--   The statement uses the same modulus in the local estimate and on $D$. It turns the uniqueness criterion in the complementarity case into a global regularity claim.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 51, paragraph immediately preceding Theorem 3.1

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

open scoped Topology

/-- Robinson, p. 51, following the local upper Lipschitz assertion. -/
theorem lipschitz_of_single_valued (r s : ℕ)
    (A : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ)
    (K : Set (EuclideanSpace ℝ (Fin s))) (hK : IsPolyhedral K) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      (∀ y₀ : EuclideanSpace ℝ (Fin r ⊕ Fin s),
        ∃ V : Set (EuclideanSpace ℝ (Fin r ⊕ Fin s)), V ∈ 𝓝 y₀ ∧
          ∀ y ∈ V, ∀ w : EuclideanSpace ℝ (Fin r ⊕ Fin s),
            y - A.toEuclideanLin w ∈ normalCone (prodSet K) w →
            ∃ w₀ : EuclideanSpace ℝ (Fin r ⊕ Fin s),
              y₀ - A.toEuclideanLin w₀ ∈ normalCone (prodSet K) w₀ ∧
              ‖w - w₀‖ ≤ lam * ‖y - y₀‖) ∧
      ∀ D : Set (EuclideanSpace ℝ (Fin r ⊕ Fin s)), Convex ℝ D →
        (∀ y ∈ D, ∃! w : EuclideanSpace ℝ (Fin r ⊕ Fin s),
          y - A.toEuclideanLin w ∈ normalCone (prodSet K) w) →
        ∀ y₁ ∈ D, ∀ y₂ ∈ D,
          ∀ w₁ w₂ : EuclideanSpace ℝ (Fin r ⊕ Fin s),
            y₁ - A.toEuclideanLin w₁ ∈ normalCone (prodSet K) w₁ →
            y₂ - A.toEuclideanLin w₂ ∈ normalCone (prodSet K) w₂ →
            ‖w₁ - w₂‖ ≤ lam * ‖y₁ - y₂‖ := by sorry

end RobinsonSR.Schur
