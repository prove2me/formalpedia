-- Prove2me | Theorems.Thm_SupplyChainTheory_lagrangian_weak_duality
-- name    : SupplyChainTheory.lagrangian_weak_duality
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:38:31.047977+00:00
-- url     : https://prove2.me/theorems/21efca42-e90e-4bcf-bcc5-23973a2843ea
-- title:
--   Eq. (8.16): $z_{LR}(\lambda) \le z^*$ for every $\lambda$
-- statement:
--   For every vector of multipliers $\lambda$ and every instance with at least one candidate site,
--
--   $$ z_{LR}(\lambda) \;\le\; z^*, $$
--
--   the optimal value of the Lagrangian subproblem is a lower bound on the optimal value of
--   (UFLP). Every feasible solution of (UFLP) is feasible for the subproblem and has the same
--   objective there, since the penalty term $\sum_i \lambda_i(1 - \sum_j y_{ij})$ vanishes when
--   (8.4) holds. This is weak Lagrangian duality (Theorem D.1 of the book) for this problem, and it
--   is what makes a feasible solution's cost and a subproblem value into a bracket on $z^*$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 274, Sect. 8.2.3.3, Eq. (8.16) ('from Theorem D.1, we know that, for any λ, the optimal objective value of (UFLP-LRλ) is a lower bound')

import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem lagrangian_weak_duality {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) (lam : Fin n → ℝ) : zLR h c f lam ≤ uflpOpt h c f := by sorry

end SupplyChainTheory
