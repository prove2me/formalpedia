-- Prove2me | Theorems.Thm_VanderbeiLP_Simplex_fundamental_theorem_lp
-- name    : VanderbeiLP.Simplex.fundamental_theorem_lp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T17:08:25.707822+00:00
-- url     : https://prove2.me/theorems/0fda3a07-8159-48e0-ac66-a3f8b99941b2
-- title:
--   Theorem 3.4 — fundamental theorem of linear programming
-- statement:
--   For an arbitrary linear program in standard form,
--   $$
--   \text{maximize } \sum_{j=1}^n c_j x_j \quad\text{subject to}\quad \sum_{j=1}^n a_{ij}x_j \le b_i\ (i = 1,\dots,m),\qquad x \ge 0,
--   $$
--   the following statements are true:
--
--   1. If there is no optimal solution, then the problem is either infeasible or unbounded.
--   2. If a feasible solution exists, then a basic feasible solution exists.
--   3. If an optimal solution exists, then a basic optimal solution exists.
--
--   Here "unbounded" means that there are feasible solutions with arbitrarily large objective values, and a solution is basic when, together with its slack variables, it is the basic solution of a dictionary.
--
--   The theorem summarizes what the terminating simplex method (Phase I and Phase II) delivers, and is the reason optimization over a polyhedron can be restricted to finitely many basic solutions.
--
--   **Formalization Note** Unboundedness is stated as "for every $M$ there is a feasible $x$ with objective value $> M$", as on p. 7, not through an extended-real supremum.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 33 (PDF 50), Theorem 3.4

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_Dictionary
import Definitions.Def_VanderbeiLP_Simplex_StandardForm

namespace VanderbeiLP.Simplex

/-- **Vanderbei, Theorem 3.4 (p. 33), fundamental theorem of linear programming.** For the
standard-form problem `maximize cᵀx s.t. Ax ≤ b, x ≥ 0`:
1. if there is no optimal solution, the problem is infeasible or unbounded;
2. if a feasible solution exists, a basic feasible solution exists;
3. if an optimal solution exists, a basic optimal solution exists. -/
theorem fundamental_theorem_lp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) :
    ((¬ ∃ x, IsOptimalSol A b c x) → IsInfeasible A b ∨ IsUnbounded A b c) ∧
    ((∃ x, IsFeasibleSol A b x) → ∃ x, IsBasicFeasibleSol A b x) ∧
    ((∃ x, IsOptimalSol A b c x) → ∃ x, IsBasicOptimalSol A b c x) := by sorry

end VanderbeiLP.Simplex
