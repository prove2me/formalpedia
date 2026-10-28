-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_interior_dual_minimum_matches_budget
-- name    : PandoraBO.Private20261023.interior_dual_minimum_matches_budget
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:14.424537+00:00
-- url     : https://prove2.me/theorems/8ead2a44-29f2-49a0-a241-a04167890429
-- title:
--   Lemma 8 — exact expected-cost matching at an interior minimum
-- statement:
--   Fix a strictly feasible expected budget $B$. If $\lambda>0$ minimizes $A_B$ over the nonnegative half-line, then some policy $\pi$ is optimal for the penalized objective and satisfies
--
--   $$C(\pi)=B.$$
--
--   Randomized policies are included. The separate Gittins cost-extrema milestone supplies the additional bridge needed to choose a budget-matching policy inside the index-policy class.
-- source:
--   Qian Xie, Raul Astudillo, Peter I. Frazier, Ziv Scully, and Alexander Terenin. [Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index](https://arxiv.org/abs/2406.20062). NeurIPS 2024. Appendix B.5, Lemma 8: budget matching at a strictly positive dual minimizer.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem interior_dual_minimum_matches_budget {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (hslater : ∃ i : Box n, M.cost i < B)
    (hmin : dualMinimizer M B multiplier) (hpos : 0 < multiplier) :
    ∃ π : Policy n, optimal M multiplier π ∧ expectedCost M π = B := by sorry

end PandoraBO.Private20261023
