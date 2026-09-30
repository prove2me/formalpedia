-- Prove2me | Theorems.Thm_SupplyChainTheory_lagrangian_equals_lp
-- name    : SupplyChainTheory.lagrangian_equals_lp
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:43:27.846904+00:00
-- url     : https://prove2.me/theorems/99ba9f92-f0b5-447b-bee8-ccbec8858074
-- title:
--   Corollary 8.2: for the UFLP, $z_{LP} = z_{LR}$
-- statement:
--   **Corollary 8.2.** For the uncapacitated fixed-charge location problem, the Lagrangian dual
--   value obtained by relaxing the assignment constraints (8.4) equals the LP relaxation value:
--
--   $$ z_{LP} \;=\; z_{LR} \;=\; \max_\lambda z_{LR}(\lambda). $$
--
--   The Lagrangian subproblem has the integrality property: for every $\lambda$ its optimal value
--   does not change when $x_j \in \{0, 1\}$ is relaxed to $0 \le x_j \le 1$, since the objective is
--   linear and, after choosing $y$ optimally for each $x$, linear in $x$. Lemma D.3 of the book
--   (Geoffrion's theorem) then gives $z_{LR} = z_{LP}$. The book draws the consequence that the
--   Lagrangian bound for the UFLP is exactly as tight as the LP bound, no more, and explains why
--   the method is still used: the subproblem is solved by inspection, and the same scheme extends
--   to nonlinear location models that LP solvers cannot handle.
--
--   **Formalization Note** $z_{LR}$ is the supremum over all real multiplier vectors; the theorem
--   asserts it equals the LP value, which is attained, so the supremum is attained as well.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 276, Sect. 8.2.3.3, Corollary 8.2 and the integrality-property discussion on p. 275; Lemma D.3 of Appendix D

import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem lagrangian_equals_lp {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) : uflpLP h c f = zLRbest h c f := by sorry

end SupplyChainTheory
