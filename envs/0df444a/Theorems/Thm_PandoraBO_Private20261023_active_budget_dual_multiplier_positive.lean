-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_active_budget_dual_multiplier_positive
-- name    : PandoraBO.Private20261023.active_budget_dual_multiplier_positive
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:10.957989+00:00
-- url     : https://prove2.me/theorems/794e4ade-7707-45b6-aa0d-0420f49da46c
-- title:
--   Positivity corollary — a strict reward gap excludes zero multipliers
-- statement:
--   Suppose some box costs less than $B$, some policy is budget feasible, and
--
--   $$R_B^*<R_{\mathrm{all}}.$$
--
--   Then every minimizer of $A_B$ on $[0,\infty)$ is strictly positive. This supporting corollary concerns the positive regime; the strict-gap assumption is absent from the main mission goal. It is a sufficient condition, not asserted necessary for existence of some positive multiplier.
-- source:
--   Qian Xie, Raul Astudillo, Peter I. Frazier, Ziv Scully, and Alexander Terenin. [Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index](https://arxiv.org/abs/2406.20062). NeurIPS 2024. Appendix B.5, the budget-duality argument for Theorem 2. This supporting corollary assumes a strict gap between the budget-constrained optimal reward and the full-information reward; that assumption is not imposed on the main theorem.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem active_budget_dual_multiplier_positive {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (hslater : ∃ i : Box n, M.cost i < B)
    (hactive : genuinelyActiveBudget M B) (hmin : dualMinimizer M B multiplier) :
    0 < multiplier := by sorry

end PandoraBO.Private20261023
