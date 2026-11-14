-- Prove2me | Theorems.Thm_QuantileMDP_theorem_6_stationary
-- name    : QuantileMDP.theorem_6_stationary
-- status  : Proved
-- author  : @shuffle
-- created : 2026-11-14T02:27:21.633109+00:00
-- url     : https://prove2.me/theorems/edf50d3a-611d-43a8-8265-40dcd22b0448
-- title:
--   Quantile MDP Theorem 6 — discounted value iteration and attainability
-- statement:
--   For a finite-state, finite-action stationary MDP with bounded rewards and discount 0 < γ < 1, start the stationary quantile Bellman iteration at zero. Use the strict allocation budget (with zero budget allowed), as in this collection's finite-horizon result. The iterates converge to the optimal lower quantile of the infinite discounted reward. At iteration n the error is at most Rγⁿ/(1−γ), simultaneously for every starting state and every quantile level in [0,1]. For each starting state and level, an admissible deterministic history-dependent policy attains the infinite-horizon value.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.3, Theorem 6, pp. 23–24. https://arxiv.org/abs/1711.05788v5

import Definitions.Def_QuantileMDP_trajectory
import Definitions.Def_QuantileMDP_discountedIteration
import Definitions.Def_QuantileMDP_quantile

open QuantileMDP MeasureTheory Filter
open scoped Topology

theorem QuantileMDP.theorem_6_stationary {S A : Type*} [Fintype S] [Fintype A]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S A)
    (hP : ∀ k, M.P k = M.P 0) (hr : ∀ k, M.r k = M.r 0) (ha : ∀ k, M.adm k = M.adm 0)
    (γ R : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hR : ∀ k s a i, |M.r k s a i| ≤ R)
    (s : S) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let Q := fun π : {π : Policy S A // M.Admissible π} =>
      quantile ((trajectoryLaw M π.val s).map (fun w => ∑' k, γ ^ k * stepReward M π.val k w)) τ
    let V := ⨆ π, Q π
    (∃ π, Q π = V) ∧ Tendsto (fun n => discountedIter M γ n s τ) atTop (𝓝 V) ∧
      ∀ n, discountedIter M γ n s τ ≤ V + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) ∧
        V ≤ discountedIter M γ n s τ + ((R * γ ^ n / (1 - γ) : ℝ) : EReal) := by sorry
