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
--   Then every minimizer of $A_B$ on $[0,\infty)$ is strictly positive. This corrected Lemma 9 is a corollary about the positive regime; the strict-gap assumption is absent from the main mission goal. It is a sufficient condition, not asserted necessary for existence of some positive multiplier.
-- source:
--   Xie, Astudillo, Frazier, Scully and Terenin, Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index, NeurIPS 2024; arXiv:2406.20062v3 (16 January 2025), https://arxiv.org/pdf/2406.20062v3. Corrected version of Appendix B.5, Lemma 9, retained only as a supporting positivity corollary. Adds R*_B < E[max_i F_i]; this is not a hypothesis of the revised main theorem. Mission source version: the author-revised manuscript reviewed on 23 October 2026, intended for arXiv v4; public posting is pending. References to arXiv v3 identify the earlier published version.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem active_budget_dual_multiplier_positive {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (hslater : ∃ i : Box n, M.cost i < B)
    (hactive : genuinelyActiveBudget M B) (hmin : dualMinimizer M B multiplier) :
    0 < multiplier := by sorry

end PandoraBO.Private20261023
