-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_zero_dual_minimum_feasible_gittins
-- name    : PandoraBO.Private20261023.zero_dual_minimum_feasible_gittins
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:18.076696+00:00
-- url     : https://prove2.me/theorems/916165b3-9cba-4891-befb-73901237857f
-- title:
--   Boundary lemma — a feasible zero-index optimum at a zero dual minimum
-- statement:
--   In the finite independent integrable box model, fix any real budget $B$. If $0$ minimizes $A_B$ over $[0,\infty)$, there exists a zero-multiplier Gittins policy $\pi_0$ satisfying
--
--   $$C(\pi_0)\le B,\qquad R(\pi_0)=R_{\mathrm{all}},\qquad \pi_0\in\arg\max_\rho R(\rho).$$
--
--   This is an existence claim for a suitable tie rule. It does not require $C(\pi_0)=B$, and does not claim every zero-index policy is budget feasible.
-- source:
--   Qian Xie, Raul Astudillo, Peter I. Frazier, Ziv Scully, and Alexander Terenin. [Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index](https://arxiv.org/abs/2406.20062). NeurIPS 2024. Appendix B.5, Lemma 9 and the zero-multiplier case of Theorem 2. This milestone isolates existence of a feasible generalized Gittins policy at a zero dual minimum.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem zero_dual_minimum_feasible_gittins {n : ℕ} (M : Instance n)
    (B : ℝ) (hmin : dualMinimizer M B 0) :
    ∃ π : Policy n, isZeroGittinsPolicy M π ∧
      budgetFeasible M B π ∧ expectedReward M π = fullInformationReward M ∧
      optimal M 0 π := by sorry

end PandoraBO.Private20261023
