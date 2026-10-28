-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_complementary_lagrangian_certificate
-- name    : PandoraBO.Private20261023.complementary_lagrangian_certificate
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-23T23:40:05.444898+00:00
-- url     : https://prove2.me/theorems/7b429502-75fb-49f4-90ae-85d8f712930e
-- title:
--   Lemma 5 extension — feasibility and complementary slackness
-- statement:
--   For any real budget $B$ and nonnegative multiplier $\lambda$, suppose a policy $\pi$ maximizes $R(\rho)-\lambda C(\rho)$ over all measurable adaptive randomized policies. If
--
--   $$C(\pi)\le B,\qquad \lambda(B-C(\pi))=0,$$
--
--   then $\pi$ is budget-optimal: every policy $\rho$ with $C(\rho)\le B$ satisfies $R(\rho)\le R(\pi)$. Unlike exact-budget matching, this sufficient condition includes $\lambda=0$ and unused budget. This is an explicit extension of Lemma 5, not a verbatim source statement.
-- source:
--   Qian Xie, Raul Astudillo, Peter I. Frazier, Ziv Scully, and Alexander Terenin. [Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index](https://arxiv.org/abs/2406.20062). NeurIPS 2024. Appendix B.5: the Lagrangian budget-optimality argument with complementary slackness, including the zero-multiplier case. This milestone isolates a proof step.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem complementary_lagrangian_certificate {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (hnonneg : 0 ≤ multiplier) (π : Policy n)
    (hopt : optimal M multiplier π) (hfeasible : budgetFeasible M B π)
    (hcomp : complementarySlackness M B multiplier π) :
    budgetOptimal M B π := by sorry

end PandoraBO.Private20261023
