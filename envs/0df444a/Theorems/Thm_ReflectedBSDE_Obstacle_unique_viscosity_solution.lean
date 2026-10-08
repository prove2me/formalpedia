-- Prove2me | Theorems.Thm_ReflectedBSDE_Obstacle_unique_viscosity_solution
-- name    : ReflectedBSDE.Obstacle.unique_viscosity_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:52.485677+00:00
-- url     : https://prove2.me/theorems/825c8d2f-39cf-40ba-a36f-12b3e3e9f78f
-- title:
--   Theorem 8.6 — uniqueness of polynomial-growth viscosity solutions
-- statement:
--   Assume the continuous §8 coefficients satisfy the stated growth and Lipschitz bounds, terminal compatibility, and spatial modulus condition (27). If $u$ and $v$ are continuous viscosity solutions of the obstacle problem (24), each with at most polynomial growth at spatial infinity, then they coincide throughout the closed time strip:
--
--   $$
--   u(t,x)=v(t,x)\qquad ((t,x)\in[0,T]\times\mathbb R^d).
--   $$
--
--   The theorem is a uniqueness assertion; it does not require a stochastic representation or assume existence of a solution.
--
--   **Formalization Note** The dimension is positive, and the bounds use an equivalent finite-dimensional norm with existential constants.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 731, Theorem 8.6

import Definitions.Def_ReflectedBSDE_Obstacle_IsSolution
import Definitions.Def_ReflectedBSDE_Obstacle_PolynomialGrowth
import Definitions.Def_ReflectedBSDE_Obstacle_HasSpatialModulus

open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- Theorem 8.6: the obstacle problem (24) has at most one continuous
viscosity solution with polynomial growth at spatial infinity. -/
theorem unique_viscosity_solution {d : ℕ} (hd : 0 < d)
    (D : Data d) (hm : HasSpatialModulus D)
    (u v : ℝ≥0 → (Fin d → ℝ) → ℝ)
    (hu : IsSolution D u) (hv : IsSolution D v)
    (hgu : PolynomialGrowth D.T u) (hgv : PolynomialGrowth D.T v) :
    ∀ t : ℝ≥0, t ≤ D.T → ∀ x : Fin d → ℝ, u t x = v t x := by sorry

end ReflectedBSDE.Obstacle
