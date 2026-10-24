-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_zero_dual_minimum_feasible_gittins
-- name    : PandoraBO.Private20261023.zero_dual_minimum_feasible_gittins
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:18.076696+00:00
-- url     : https://prove2.me/theorems/916165b3-9cba-4891-befb-73901237857f
-- title:
--   New boundary lemma — a feasible zero-index optimum at a zero dual minimum
-- statement:
--   Fix any real budget $B$. If $0$ minimizes $A_B$ over $[0,\infty)$, there exists a zero-multiplier Gittins policy $\pi_0$ satisfying
--
--   $$C(\pi_0)\le B,\qquad R(\pi_0)=R_{\mathrm{all}},\qquad \pi_0\in\arg\max_\rho R(\rho).$$
--
--   This is an existence claim for a suitable tie rule. It does not require $C(\pi_0)=B$, and does not claim every zero-index policy is budget feasible. The only additional hypothesis beyond the standing finite independent integrable model is that zero is a dual minimizer; strict feasibility and a reward gap are not assumed.
-- source:
--   Xie, Astudillo, Frazier, Scully and Terenin, Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index, NeurIPS 2024; arXiv:2406.20062v3 (16 January 2025), https://arxiv.org/pdf/2406.20062v3. Proposed new replacement for the missing zero branch of Theorem 2 / Appendix B.5, Lemma 9. Not a verbatim source lemma. Mission source version: the author-revised manuscript reviewed on 23 October 2026, intended for arXiv v4; public posting is pending. References to arXiv v3 identify the earlier published version.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem zero_dual_minimum_feasible_gittins {n : ℕ} (M : Instance n)
    (B : ℝ) (hmin : dualMinimizer M B 0) :
    ∃ π : Policy n, isZeroGittinsPolicy M π ∧
      budgetFeasible M B π ∧ expectedReward M π = fullInformationReward M ∧
      optimal M 0 π := by sorry

end PandoraBO.Private20261023
