-- Prove2me | Theorems.Thm_StochasticRewardMatching_Decomposable_lemma_1
-- name    : StochasticRewardMatching.Decomposable.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:18:42.167727+00:00
-- url     : https://prove2.me/theorems/92ef22e5-d259-4456-be21-c94b4338d813
-- title:
--   Lemma 1 — Deterministic adaptive benchmark and DP attainment
-- statement:
--   For every source instance, the concrete deterministic policy obtained from the dynamic program attains the randomized benchmark, separately for clairvoyant and fully offline. Its expected reward equals the recursively computed initial DP value in both cases. Fully offline can adaptively choose any remaining arrival; clairvoyant processes the earliest remaining arrival. Both may discard or stop.
--
--   Lemma 1. The optimal fully offline and clairvoyant algorithms are deterministic and given by a (possibly exponential time) dynamic program.
--
--   Differences from the source:
--   - encoding: arbitrary finite resources and ordered arrivals with nonnegative vertex rewards → Fin n and Fin m for arbitrary natural n,m, with nonnegative real rewards and present-edge probabilities in [0,1]; reason: labeling preserves every finite instance, including empty cases, without bounding sizes or rewards
--   - encoding: possibly randomized adaptive offline algorithms → all probability kernels on finite next actions given the complete observed history, with invalid proposals stopped; reason: conditional action distributions represent arbitrary private randomness in this finite perfect-recall problem; valid policies are unchanged and no foresight is provided
--   - encoding: dynamic program in Appendix A.2, with termination and no feasible offer implicit → finite recursion with explicit discard and stop actions, terminal zero, and a deterministic maximizing policy; reason: these actions complete the source model at isolated arrivals and empty states; DP attainment is a conclusion
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), Lemma 1, PDF/printed p. 9; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_DynamicProgram

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

theorem lemma_1 {n m : ℕ} (D : Instance n m) :
    (deterministicValue D true (dpPolicy D true) = dp D true m Finset.univ Finset.univ ∧
      benchmark D true = deterministicValue D true (dpPolicy D true)) ∧
    (deterministicValue D false (dpPolicy D false) = dp D false m Finset.univ Finset.univ ∧
      benchmark D false = deterministicValue D false (dpPolicy D false)) := by sorry

end StochasticRewardMatching.Decomposable
