-- Prove2me | Theorems.Thm_StochasticRewardMatching_Decomposable_lemma_5
-- name    : StochasticRewardMatching.Decomposable.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:18:30.78299+00:00
-- url     : https://prove2.me/theorems/57a6d5d0-4a8a-4859-a569-63df5189eaa8
-- title:
--   Lemma 5 — Arrival-side conditional lower bound, both clauses
-- statement:
--   Fix any present edge, every other edge outcome, and every other seed in [0,1]. Using the literal printed threshold, the single-edge conditional expected arrival dual value is at least p_it r_i(1-g(y_i^c)) for every y_i in [0,1], and the same lower bound holds after averaging y_i uniformly. The source assertion is retained although I1 supplies a counterexample.
--
--   Lemma 5. Given edge (i,t), sample path ω₋ᵢₜ, seed Y₋ᵢ, we have E_ω[λₜ^{ω,Y}] ≥ pᵢₜrᵢ(1 − g(yᵢᶜ)) for every yᵢ ∈ [0,1]. Thus, E_{yᵢ}[E_ω[λᵢ^{ω,Y}]] ≥ pᵢₜrᵢ(1 − g(yᵢᶜ)).
--
--   Differences from the source:
--   - encoding: arbitrary finite resources and ordered arrivals with nonnegative vertex rewards → Fin n and Fin m for arbitrary natural n,m, with nonnegative real rewards and present-edge probabilities in [0,1]; reason: labeling preserves every finite instance, including empty cases, without bounding sizes or rewards
--   - encoding: i.i.d. uniform real seeds and independent Bernoulli edge outcomes → product restricted Lebesgue measure on [0,1], finite Bernoulli sums, and least-index ties in Algorithm 1; reason: these are the same laws; the fixed order remains consistent under deletion and completes zero-score cases
--   - encoding: partial path omega_-it and fixed other seeds Y_-i → full vectors whose distinguished coordinates are overwritten or ignored; reason: all other coordinates stay fixed, even on null outside paths; the extension values have no effect
--   - reading: the printed threshold equation has a unique solution → select its largest solution in [0,1] when there are multiple roots; reason: zero probability or reward can make every value a root; this resolves only the unspecified choice, preserving the printed missing r_j and both source findings
--   - reading: lambda_i in the second clause → lambda_t for the distinguished arrival; reason: the preceding shorthand on p. 15 explicitly defines lambda_i as lambda_t
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), Lemma 5, PDF/printed p. 15; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Dual
import Definitions.Def_StochasticRewardMatching_Decomposable_Threshold

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

theorem lemma_5 {n m : ℕ} (D : Instance n m) (e : Edge D)
    (ω : Outcome D) (Y : Seeds n)
    (hY : ∀ j, j ≠ e.val.1 → Y j ∈ Set.Icc (0 : ℝ) 1) :
    (∀ y ∈ Set.Icc (0 : ℝ) 1,
      D.probability e.val * D.reward e.val.1 * (1 - g (threshold D e ω Y)) ≤
        resample D e ω (fun w => lambdaPath D w (Function.update Y e.val.1 y) e.val.2)) ∧
    D.probability e.val * D.reward e.val.1 * (1 - g (threshold D e ω Y)) ≤
      oneSeedAverage e.val.1 Y (fun Z => resample D e ω (fun w => lambdaPath D w Z e.val.2)) := by sorry

end StochasticRewardMatching.Decomposable
