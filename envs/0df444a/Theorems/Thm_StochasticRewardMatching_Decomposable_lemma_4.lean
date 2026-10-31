-- Prove2me | Theorems.Thm_StochasticRewardMatching_Decomposable_lemma_4
-- name    : StochasticRewardMatching.Decomposable.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:18:10.797677+00:00
-- url     : https://prove2.me/theorems/63396705-f785-4933-8e9d-ad93ca86ceeb
-- title:
--   Lemma 4 — Averaging the other seeds
-- statement:
--   Fix a present edge. If equation (10), using the actual pathwise dual variables, holds for every outside path and every fixed other seed vector, then the seed-averaged dual variables satisfy equation (8) on that edge with alpha=1-1/e. The implication assumes exactly its printed conditional bound, not a performance hypothesis for the main goal.
--
--   Lemma 4. Consider an edge (i,t) ∈ E. Suppose that for the dual fitting given by (9), for every sample path ω₋ᵢₜ and values yⱼ for all j ≠ i, denoted Y₋ᵢ, we have,
--
--   E_{yᵢ}[E_ω[λₜ^{ω,Y} + θᵢ^{ω,Y} 1^ω(i,t) | ω₋ᵢₜ] | Y₋ᵢ] ≥ (1 − 1/e)pᵢₜrᵢ. (10)
--
--   Then, inequality (8) is satisfied for edge (i,t) with α = (1 − 1/e).
--
--   Differences from the source:
--   - encoding: arbitrary finite resources and ordered arrivals with nonnegative vertex rewards → Fin n and Fin m for arbitrary natural n,m, with nonnegative real rewards and present-edge probabilities in [0,1]; reason: labeling preserves every finite instance, including empty cases, without bounding sizes or rewards
--   - encoding: i.i.d. uniform real seeds and independent Bernoulli edge outcomes → product restricted Lebesgue measure on [0,1], finite Bernoulli sums, and least-index ties in Algorithm 1; reason: these are the same laws; the fixed order remains consistent under deletion and completes zero-score cases
--   - encoding: partial path omega_-it and fixed other seeds Y_-i → full vectors whose distinguished coordinates are overwritten or ignored; reason: all other coordinates stay fixed, even on null outside paths; the extension values have no effect
--   - encoding: 1-1/e → 1-Real.exp(-1); reason: the constants are equal
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), Lemma 4, PDF/printed p. 15; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Dual

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

theorem lemma_4 {n m : ℕ} (D : Instance n m) (e : Edge D)
    (hconditional : ∀ (ω : Outcome D) (Y : Seeds n),
      (∀ j, j ≠ e.val.1 → Y j ∈ Set.Icc (0 : ℝ) 1) →
      (1 - Real.exp (-1)) * D.probability e.val * D.reward e.val.1 ≤
        oneSeedAverage e.val.1 Y (fun Z => resample D e ω
          (fun w => lambdaPath D w Z e.val.2 + thetaPath D w Z e.val.1 * indicator w e))) :
    ∀ ω : Outcome D,
      (1 - Real.exp (-1)) * D.probability e.val * D.reward e.val.1 ≤
        resample D e ω (fun w => lambda D w e.val.2 + theta D w e.val.1 * indicator w e) := by sorry

end StochasticRewardMatching.Decomposable
