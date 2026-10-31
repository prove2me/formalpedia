-- Prove2me | Theorems.Thm_StochasticRewardMatching_Decomposable_theorem_1
-- name    : StochasticRewardMatching.Decomposable.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:17:17.873307+00:00
-- url     : https://prove2.me/theorems/732414eb-5ef3-4cbe-a6fd-4f5b2b1f17be
-- title:
--   Theorem 1 — Optimal competitiveness of generalized perturbed greedy
-- statement:
--   For every finite source-model instance with decomposable probabilities, actual Algorithm 1 earns in expectation at least (1-1/e) times each of the optimal clairvoyant and fully offline expected rewards. All randomization in the algorithm and benchmarks is included. Moreover, for every epsilon>0 and every randomized online algorithm family, some finite decomposable instance with positive values for both benchmarks makes its expected reward at most (1-1/e+epsilon) times each benchmark. No performance, optimality or dual feasibility certificate is assumed.
--
--   Theorem 1. For decomposable probabilities pᵢₜ = pᵢpₜ ∀(i,t) ∈ E, Algorithm 1 is (1 − 1/e) competitive against offline (both clairvoyant and fully offline). This is the best possible competitive ratio guarantee.
--
--   Differences from the source:
--   - encoding: arbitrary finite resources and ordered arrivals with nonnegative vertex rewards → Fin n and Fin m for arbitrary natural n,m, with nonnegative real rewards and present-edge probabilities in [0,1]; reason: labeling preserves every finite instance, including empty cases, without bounding sizes or rewards
--   - encoding: i.i.d. uniform real seeds and independent Bernoulli edge outcomes → product restricted Lebesgue measure on [0,1], finite Bernoulli sums, and least-index ties in Algorithm 1; reason: these are the same laws; the fixed order remains consistent under deletion and completes zero-score cases
--   - encoding: possibly randomized adaptive offline algorithms → all probability kernels on finite next actions given the complete observed history, with invalid proposals stopped; reason: conditional action distributions represent arbitrary private randomness in this finite perfect-recall problem; valid policies are unchanged and no foresight is provided
--   - encoding: 1-1/e → 1-Real.exp(-1); reason: the constants are equal
--   - encoding: best possible competitive ratio against both benchmarks → for every epsilon>0 and every randomized online algorithm family, there is a finite decomposable instance with both optima positive and expected online reward at most (1-1/e+epsilon) times each optimum; reason: this is the usual uniform competitive-ratio upper bound; a classical unit-probability hard instance has identical benchmarks, and the algorithm is quantified before the instance
--   - encoding: general randomized online algorithms → history-dependent probability kernels on resource-or-skip actions for every finite size, with future input rows hidden; reason: conditional action laws include algorithms with arbitrary private randomness and memory; horizon knowledge is allowed and finite random seeds are not imposed
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), Theorem 1, PDF/printed p. 5; proof p. 17; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Algorithm
import Definitions.Def_StochasticRewardMatching_Decomposable_Benchmarks
import Definitions.Def_StochasticRewardMatching_Decomposable_OnlinePolicies

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

theorem theorem_1 :
    (∀ (n m : ℕ) (D : Instance n m), decomposable D →
      (1 - Real.exp (-1)) * benchmark D true ≤ algorithmValue D ∧
      (1 - Real.exp (-1)) * benchmark D false ≤ algorithmValue D) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ A : OnlineFamily,
      ∃ (n m : ℕ) (D : Instance n m), decomposable D ∧
        0 < benchmark D true ∧ 0 < benchmark D false ∧
        onlineValue D (A n m) ≤ (1 - Real.exp (-1) + ε) * benchmark D true ∧
        onlineValue D (A n m) ≤ (1 - Real.exp (-1) + ε) * benchmark D false) := by sorry

end StochasticRewardMatching.Decomposable
