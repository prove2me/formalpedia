-- Prove2me | Theorems.Thm_SupplyChainTheory_lagrangian_dual_bounds
-- name    : SupplyChainTheory.lagrangian_dual_bounds
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:38:56.920292+00:00
-- url     : https://prove2.me/theorems/db04bef3-e4e7-47c3-a8dc-f923da9c745b
-- title:
--   Eq. (8.19): $z_{LP} \le z_{LR} \le z^*$
-- statement:
--   With $z_{LR} = \max_\lambda z_{LR}(\lambda)$ the Lagrangian dual value (8.17), for every
--   instance with at least one candidate site,
--
--   $$ z_{LP} \;\le\; z_{LR} \;\le\; z^*. $$
--
--   The right inequality is (8.16) taken over all $\lambda$; the left is Theorem D.2 of the book,
--   that the Lagrangian dual is at least as tight as the LP relaxation, because for each $\lambda$
--   the subproblem value is bounded by the value of the same Lagrangian over the LP-relaxed set,
--   and LP duality bounds that by $z_{LP}$. Corollary 8.2 sharpens the left inequality to an
--   equality.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 275, Sect. 8.2.3.3, Eq. (8.18)-(8.19) ('Combining (8.16) and (8.18), we now know that zLP ≤ zLR ≤ z∗')

import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem lagrangian_dual_bounds {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) : uflpLP h c f ≤ zLRbest h c f ∧ zLRbest h c f ≤ uflpOpt h c f := by sorry

end SupplyChainTheory
