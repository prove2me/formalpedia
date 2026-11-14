-- Prove2me | Theorems.Thm_QuantileMDP_discounted_augmented_policy_bound
-- name    : QuantileMDP.discounted_augmented_policy_bound
-- status  : Proved
-- author  : @shuffle
-- created : 2026-11-14T02:38:10.243026+00:00
-- url     : https://prove2.me/theorems/294ae35a-bee7-417c-b9f3-58cd43d57ef4
-- title:
--   Quantile MDP — finite-horizon augmented policy approximates the infinite optimum
-- statement:
--   In a finite-state, finite-action MDP with rewards bounded in absolute value by R and discount 0 ≤ γ < 1, use the finite-horizon augmented-state policy from Theorem 3 for n steps and continue admissibly. For each starting state and quantile level the resulting infinite-horizon quantile is within 2Rγⁿ/(1−γ) of the infinite optimum. This is an approximate execution result related to the infinite-horizon policy question in Theorem 7, and it uses only the finite-horizon allocation optimizers. Time-dependent transition laws, rewards, and admissible actions are allowed.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.3, following Theorem 7, pp. 23–24. https://arxiv.org/abs/1711.05788v5

import Definitions.Def_QuantileMDP_trajectory
import Definitions.Def_QuantileMDP_augmentedPolicy
import Definitions.Def_QuantileMDP_quantile

open MeasureTheory Set QuantileMDP

theorem QuantileMDP.discounted_augmented_policy_bound {S A : Type*} [Fintype S] [Fintype A]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S A)
    (γ R : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (hR : ∀ k s a i, |M.r k s a i| ≤ R) (n : ℕ) :
    ∃ (act : ℕ → S → ℝ → A) (next : ℕ → S → ℝ → S → ℝ),
      ∀ s τ, τ ∈ Icc (0 : ℝ) 1 →
        let π := augmentedPolicy act next 0 τ
        M.Admissible π ∧
        (⨆ ρ : {ρ : Policy S A // M.Admissible ρ},
          quantile ((trajectoryLaw M ρ.val s).map
            (fun w => ∑' k, γ ^ k * stepReward M ρ.val k w)) τ) ≤
          quantile ((trajectoryLaw M π s).map (fun w => ∑' k, γ ^ k * stepReward M π k w)) τ +
            ((2 * (R * γ ^ n / (1 - γ)) : ℝ) : EReal) := by sorry
