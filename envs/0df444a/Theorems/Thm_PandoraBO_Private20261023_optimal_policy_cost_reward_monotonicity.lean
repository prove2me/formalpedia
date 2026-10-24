-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_optimal_policy_cost_reward_monotonicity
-- name    : PandoraBO.Private20261023.optimal_policy_cost_reward_monotonicity
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:54:28.912004+00:00
-- url     : https://prove2.me/theorems/7a96fc1b-0ce0-4b8b-a91e-6f1593021bc3
-- title:
--   Optimal expected cost and reward decrease with the cost multiplier
-- statement:
--   For two real cost multipliers 0≤s<t, let π be globally optimal at s and ρ globally optimal at t. Then the expected cost of ρ is at most that of π, and its expected reward is also at most that of π. The claim holds for any choices of these optimizers.
-- source:
--   Supporting monotonicity argument in Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5, proof of Lemma 7 (equation (43) and the final subsequence argument on page 22). Isolated algebraic/analytic auxiliary lemma for formalization.

import Definitions.Def_PandoraBO_Model
open PandoraBO
set_option autoImplicit false

theorem PandoraBO.Private20261023.optimal_policy_cost_reward_monotonicity {n : ℕ} (M : Instance n) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s < t) (π ρ : Policy n)
    (hπ : optimal M s π) (hρ : optimal M t ρ) :
    expectedCost M ρ ≤ expectedCost M π ∧
      expectedReward M ρ ≤ expectedReward M π := by sorry
