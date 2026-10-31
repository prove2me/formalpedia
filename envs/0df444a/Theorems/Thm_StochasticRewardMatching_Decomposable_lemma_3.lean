-- Prove2me | Theorems.Thm_StochasticRewardMatching_Decomposable_lemma_3
-- name    : StochasticRewardMatching.Decomposable.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:17:53.644992+00:00
-- url     : https://prove2.me/theorems/b1afc12c-24e0-4eea-b61b-adbb1454ade0
-- title:
--   Lemma 3 — Reward equals the constructed dual total
-- statement:
--   For every source instance, the expected sum of the seed-averaged dual variables constructed by equation (9) equals the actual expected reward of Algorithm 1, averaged over both seeds and independent edge outcomes. No decomposability is needed for this accounting identity.
--
--   Lemma 3. For the candidate solution given by (9), equality (7) is satisfied.
--
--   Differences from the source:
--   - encoding: arbitrary finite resources and ordered arrivals with nonnegative vertex rewards → Fin n and Fin m for arbitrary natural n,m, with nonnegative real rewards and present-edge probabilities in [0,1]; reason: labeling preserves every finite instance, including empty cases, without bounding sizes or rewards
--   - encoding: i.i.d. uniform real seeds and independent Bernoulli edge outcomes → product restricted Lebesgue measure on [0,1], finite Bernoulli sums, and least-index ties in Algorithm 1; reason: these are the same laws; the fixed order remains consistent under deletion and completes zero-score cases
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), Lemma 3, PDF/printed p. 14; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Dual

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

theorem lemma_3 {n m : ℕ} (D : Instance n m) :
    dualTotal D (lambda D) (theta D) = algorithmValue D := by sorry

end StochasticRewardMatching.Decomposable
