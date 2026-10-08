-- Prove2me | Theorems.Thm_RobinsonSR_Schur_upper_lipschitz_polyhedral
-- name    : RobinsonSR.Schur.upper_lipschitz_polyhedral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:02:19.289616+00:00
-- url     : https://prove2.me/theorems/24fa88e6-029c-4e26-ba4f-9def3272c854
-- title:
--   Polyhedral inverse multifunction is locally upper Lipschitz
-- statement:
--   Let $K\subseteq\mathbb R^s$ be polyhedral and let $T(w)=Aw+N_{\mathbb R^r\times K}(w)$. There is one constant $\lambda\geq0$ such that, for every $y_0$, a neighborhood $V$ of $y_0$ satisfies
--
--   $$
--   T^{-1}(y)\subseteq T^{-1}(y_0)+\lambda\|y-y_0\|B\qquad(y\in V),
--   $$
--
--   where $B$ is the Euclidean unit ball. The same $\lambda$ works at every base point; $V$ may depend on $y_0$. This supplies the uniform local estimate used in the polyhedral case.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), pp. 50–51, citing [12, Proposition 2]

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

open scoped Topology

/-- Robinson, p. 50-51, citing [12, Proposition 2]. -/
theorem upper_lipschitz_polyhedral (r s : ℕ)
    (A : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ)
    (K : Set (EuclideanSpace ℝ (Fin s))) (hK : IsPolyhedral K) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      ∀ y₀ : EuclideanSpace ℝ (Fin r ⊕ Fin s),
        ∃ V : Set (EuclideanSpace ℝ (Fin r ⊕ Fin s)), V ∈ 𝓝 y₀ ∧
          ∀ y ∈ V, ∀ w : EuclideanSpace ℝ (Fin r ⊕ Fin s),
            y - A.toEuclideanLin w ∈ normalCone (prodSet K) w →
            ∃ w₀ : EuclideanSpace ℝ (Fin r ⊕ Fin s),
              y₀ - A.toEuclideanLin w₀ ∈ normalCone (prodSet K) w₀ ∧
              ‖w - w₀‖ ≤ lam * ‖y - y₀‖ := by sorry

end RobinsonSR.Schur
