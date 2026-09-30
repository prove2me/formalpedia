-- Prove2me | Theorems.Thm_SupplyChainTheory_lagrangian_subproblem
-- name    : SupplyChainTheory.lagrangian_subproblem
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:37:30.854324+00:00
-- url     : https://prove2.me/theorems/ade4e55b-f6fd-4295-afc7-afec4ca08f06
-- title:
--   Theorem 8.1: $(\bar x, \bar y)$ solves (UFLP-LR$_\lambda$) and $z_{LR}(\lambda) = \sum_j \min\{0, \beta_j + f_j\} + \sum_i \lambda_i$
-- statement:
--   **Theorem 8.1.** For any multipliers $\lambda$, let $\beta_j = \sum_i \min\{0, h_i c_{ij} - \lambda_i\}$
--   and set $\bar x_j = 1$ if $\beta_j + f_j < 0$ and $0$ otherwise (8.14), and $\bar y_{ij} = 1$ if
--   $\bar x_j = 1$ and $h_i c_{ij} - \lambda_i < 0$ and $0$ otherwise (8.15). Then $(\bar x, \bar y)$ is
--   feasible and optimal for the Lagrangian subproblem (UFLP-LR$_\lambda$), and its objective value,
--   the optimal value $z_{LR}(\lambda)$, is
--
--   $$ z_{LR}(\lambda) \;=\; \sum_{j \in J} \min\{0, \beta_j + f_j\} + \sum_{i \in I} \lambda_i. $$
--
--   The subproblem decomposes by facility: opening $j$ lets every customer with negative reduced
--   cost $h_i c_{ij} - \lambda_i$ be assigned to it, so $j$ is worth opening exactly when its
--   benefit outweighs its fixed cost. Customers may end up assigned to no facility or to several,
--   since (8.4) has been relaxed.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 274, Sect. 8.2.3.2, Theorem 8.1, Eq. (8.13)-(8.15)

import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem lagrangian_subproblem {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) :
    LagrFeasible (lagrX h c f lam) (lagrY h c f lam)
      ∧ lagrObjective h c f lam (lagrX h c f lam) (lagrY h c f lam)
          = ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i
      ∧ zLR h c f lam = ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i := by sorry

end SupplyChainTheory
