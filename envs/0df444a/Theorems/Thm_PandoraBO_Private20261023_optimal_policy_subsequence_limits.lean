-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_optimal_policy_subsequence_limits
-- name    : PandoraBO.Private20261023.optimal_policy_subsequence_limits
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:14.649249+00:00
-- url     : https://prove2.me/theorems/0d98c421-e696-446b-ba36-00dad5e750bc
-- title:
--   Lift an optimal-policy expectation subsequence limit to the full sequence
-- statement:
--   Consider optimal policies chosen consistently at equal nonnegative multipliers. Along a monotone multiplier sequence, convergence of expected cost and reward on a strictly increasing subsequence implies convergence of the full expected cost and reward sequences to the same limits. The equal-multiplier consistency condition prevents arbitrary switching among ties on plateaus.
-- source:
--   Auxiliary scalar convergence argument for the private formalization of finite-policy multiplier limits in Xie et al., author revised manuscript reviewed 23 October 2026.

import Definitions.Def_PandoraBO_Model
open PandoraBO Filter Topology
set_option autoImplicit false

theorem PandoraBO.Private20261023.optimal_policy_subsequence_limits {n : ℕ} (M : Instance n)
    (multipliers : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ multipliers k)
    (policies : ℕ → Policy n)
    (hopt : ∀ k, optimal M (multipliers k) (policies k))
    (hsame : ∀ j k, multipliers j = multipliers k → policies j = policies k)
    (hmono : Monotone multipliers ∨ Antitone multipliers)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (costLimit rewardLimit : ℝ)
    (hcost : Tendsto (fun k => expectedCost M (policies (φ k))) atTop (𝓝 costLimit))
    (hreward : Tendsto (fun k => expectedReward M (policies (φ k))) atTop (𝓝 rewardLimit)) :
    Tendsto (fun k => expectedCost M (policies k)) atTop (𝓝 costLimit) ∧
      Tendsto (fun k => expectedReward M (policies k)) atTop (𝓝 rewardLimit)  := by sorry
