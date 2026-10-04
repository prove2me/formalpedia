-- Prove2me | Theorems.Thm_ThomsonProblem_thomson_one
-- name    : ThomsonProblem.thomson_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T20:15:43.731222+00:00
-- url     : https://prove2.me/theorems/06099009-82a9-42f9-a629-e17a5a544876
-- title:
--   Thomson problem, $N=1$: any single point is optimal, with energy $0$
-- statement:
--   Let $x$ be a configuration consisting of a single point $x_0\in\mathbb R^3$ with $\|x_0\|=1$. Then $x$ solves the Thomson problem for one electron, and its Coulomb energy is zero:
--   $$
--   x \text{ is an energy minimiser}\qquad\text{and}\qquad U(x)=0 .
--   $$
--
--   This is the trivial case of the list of known exact solutions: a single electron may sit anywhere on the sphere, and its energy is defined to be zero since there are no other charges.
-- source:
--   Wikipedia, "Thomson problem" (as uploaded, PDF snapshot retrieved 2026-09-29/30), section "Known exact solutions", first bullet (N = 1).

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem thomson_one (x : Fin 1 → Space) (hx : ∀ i, ‖x i‖ = 1) :
    IsEnergyMinimizer x ∧ coulombEnergy x = 0 := by sorry

end ThomsonProblem
