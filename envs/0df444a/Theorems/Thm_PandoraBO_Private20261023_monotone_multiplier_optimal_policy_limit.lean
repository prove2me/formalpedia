-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_monotone_multiplier_optimal_policy_limit
-- name    : PandoraBO.Private20261023.monotone_multiplier_optimal_policy_limit
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:12.726065+00:00
-- url     : https://prove2.me/theorems/b82df137-cb10-4cad-a451-88eec8ee527e
-- title:
--   Lemma 7 strengthening — joint reward and cost convergence at positive limits
-- statement:
--   Let positive multipliers $\lambda_k$ converge monotonically, in either direction, to a positive limit $\lambda$. There exist Gittins policies $\pi_k$ at $\lambda_k$ and a Gittins policy $\pi$ at $\lambda$ such that, for the same choices of policies,
--
--   $$C(\pi_k)\to C(\pi),\qquad R(\pi_k)\to R(\pi).$$
--
--   By Theorem 1 these policies are penalized-optimal. Joint convergence implies convergence of their values at every fixed real evaluation multiplier, with the same witnesses, and gives convergence of slopes $-C(\pi_k)$. This formalization strengthens Lemma 7 by tracking expected costs as well as rewards. It does not assert convergence of policy functions.
-- source:
--   Qian Xie, Raul Astudillo, Peter I. Frazier, Ziv Scully, and Alexander Terenin. [Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index](https://arxiv.org/abs/2406.20062). NeurIPS 2024. Appendix B.5, Lemma 7, and Appendix B.6, Lemma 13. This formalization tracks joint expected-cost and expected-reward limits, strengthening the policy-limit statement to supply the slopes used in the envelope argument.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem monotone_multiplier_optimal_policy_limit {n : ℕ} (M : Instance n)
    (multipliers : ℕ → ℝ) (limit : ℝ)
    (hpos : ∀ k, 0 < multipliers k) (hlimitpos : 0 < limit)
    (hmono : Monotone multipliers ∨ Antitone multipliers)
    (hlim : Filter.Tendsto multipliers Filter.atTop (nhds limit)) :
    ∃ policies : ℕ → Policy n, ∃ π : Policy n,
      (∀ k, isGittinsPolicy M (multipliers k) (policies k)) ∧
      isGittinsPolicy M limit π ∧
      Filter.Tendsto (fun k => expectedCost M (policies k))
        Filter.atTop (nhds (expectedCost M π)) ∧
      Filter.Tendsto (fun k => expectedReward M (policies k))
        Filter.atTop (nhds (expectedReward M π)) := by sorry

end PandoraBO.Private20261023
