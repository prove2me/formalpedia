-- Prove2me | Theorems.Thm_StochasticRewardMatching_Decomposable_lemma_6
-- name    : StochasticRewardMatching.Decomposable.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:18:47.13853+00:00
-- url     : https://prove2.me/theorems/edacf8b2-765d-4f65-9a3c-736c48dea356
-- title:
--   Lemma 6 — Resource-side conditional lower bound
-- statement:
--   For a decomposable source instance, fix a present edge, every other outcome, and every other seed in [0,1]. Using the literal printed critical threshold, the average over y_i of the single-edge resampling expectation of theta_i times the distinguished success indicator is at least p_it r_i times the integral of exp(x-1) from zero to that threshold. The source assertion is retained although I2 supplies a counterexample.
--
--   Lemma 6. Given edge (i,t), sample path ω₋ᵢₜ, seed Y₋ᵢ and decomposable edge probabilities pᵢₜ = pᵢpₜ ∀(i,t) ∈ E, we have E_{yᵢ}[E_ω[θᵢ^{ω,Y} 1^ω(i,t)]] ≥ pᵢₜrᵢ ∫₀^{yᵢᶜ} g(x)dx.
--
--   Differences from the source:
--   - encoding: arbitrary finite resources and ordered arrivals with nonnegative vertex rewards → Fin n and Fin m for arbitrary natural n,m, with nonnegative real rewards and present-edge probabilities in [0,1]; reason: labeling preserves every finite instance, including empty cases, without bounding sizes or rewards
--   - encoding: i.i.d. uniform real seeds and independent Bernoulli edge outcomes → product restricted Lebesgue measure on [0,1], finite Bernoulli sums, and least-index ties in Algorithm 1; reason: these are the same laws; the fixed order remains consistent under deletion and completes zero-score cases
--   - encoding: partial path omega_-it and fixed other seeds Y_-i → full vectors whose distinguished coordinates are overwritten or ignored; reason: all other coordinates stay fixed, even on null outside paths; the extension values have no effect
--   - reading: the printed threshold equation has a unique solution → select its largest solution in [0,1] when there are multiple roots; reason: zero probability or reward can make every value a root; this resolves only the unspecified choice, preserving the printed missing r_j and both source findings
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), Lemma 6, PDF/printed p. 16; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Dual
import Definitions.Def_StochasticRewardMatching_Decomposable_Threshold

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

theorem lemma_6 {n m : ℕ} (D : Instance n m) (hdec : decomposable D)
    (e : Edge D) (ω : Outcome D) (Y : Seeds n)
    (hY : ∀ j, j ≠ e.val.1 → Y j ∈ Set.Icc (0 : ℝ) 1) :
    D.probability e.val * D.reward e.val.1 * (∫ x in (0 : ℝ)..threshold D e ω Y, g x) ≤
      oneSeedAverage e.val.1 Y (fun Z => resample D e ω (fun w => thetaPath D w Z e.val.1 * indicator w e)) := by sorry

end StochasticRewardMatching.Decomposable
