-- Prove2me | Theorems.Thm_SupplyChainTheory_variable_fixing
-- name    : SupplyChainTheory.variable_fixing
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:39:32.180918+00:00
-- url     : https://prove2.me/theorems/d77809de-354e-4568-98b4-e686b9093ecc
-- title:
--   Theorem 8.3: variable fixing from the Lagrangian bounds, $x_j = 0$ or $x_j = 1$ in every optimal solution
-- statement:
--   **Theorem 8.3.** Let $UB$ be an upper bound on $z^*$ (the cost of any feasible solution), let
--   $\lambda$ be any multipliers, $\beta_j$ the benefits (8.13) under $\lambda$ and $z_{LR}(\lambda)$
--   the subproblem value. If $x_j = 0$ in the solution (8.14) to (UFLP-LR$_\lambda$), that is
--   $\beta_j + f_j \ge 0$, and
--
--   $$ z_{LR}(\lambda) + \beta_j + f_j > UB, $$
--
--   then $x_j = 0$ in every optimal solution to (UFLP); if $x_j = 1$ in that solution, that is
--   $\beta_j + f_j < 0$, and $z_{LR}(\lambda) - (\beta_j + f_j) > UB$, then $x_j = 1$ in every optimal
--   solution. The two quantities are the subproblem values with $x_j$ forced to $1$ and to $0$;
--   a feasible solution on the other side of the branch costs at least that much, so more than
--   $UB \ge z^*$, and cannot be optimal. These tests fix variables before branch-and-bound.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 280-281, Sect. 8.2.3.7, Theorem 8.3 and its proof, Eq. (8.23)-(8.24)

import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem variable_fixing {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) (lam : Fin n → ℝ) (UB : ℝ) (hUB : uflpOpt h c f ≤ UB) (j : Fin m) :
    (0 ≤ benefit h c lam j + f j → UB < zLR h c f lam + (benefit h c lam j + f j) →
        ∀ x y, UFLPFeasible x y → uflpCost h c f x y = uflpOpt h c f → x j = 0)
      ∧ (benefit h c lam j + f j < 0 → UB < zLR h c f lam - (benefit h c lam j + f j) →
        ∀ x y, UFLPFeasible x y → uflpCost h c f x y = uflpOpt h c f → x j = 1) := by sorry

end SupplyChainTheory
