-- Prove2me | Theorems.Thm_UnknownCovDP_General_lemma_2_4
-- name    : UnknownCovDP.General.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:36.653642+00:00
-- url     : https://prove2.me/theorems/480124e1-b1e0-4343-8a6f-0a9bdef95580
-- title:
--   Lemma 2.4 — from mean estimation to sampling
-- statement:
--   There is a constant $c>0$ such that for all $d,k,n$ with $n\ge1$, $n\le ck$ and $k\le d$ the following holds. If $\mathcal A$ is a $(1,c/n)$-differentially private algorithm satisfying
--   $$\Pr_{(\mu,\Sigma)\sim\mathcal P_{\mathrm{sub}},\ X\sim N(\mu,\Sigma)^{\otimes n},\ \text{coins of }\mathcal A}\bigl[\|\mathcal A(X)-\mu\|_2\le\alpha\bigr]\ge\frac34,$$
--   then there is a $(ck/n,\alpha)$-sampler for $\mathcal P_{\mathrm{sub}}$ with sample complexity $n$ that is $(1,c/n)$-differentially private.
--
--   This reduces the mean-estimation lower bound to the sampling lower bound of Theorem 2.3.
--
--   Differences from the source:
--   - encoding: n ∈ ℕ a sample size, with c/n in the statement → hypothesis 1 ≤ n; reason: c/n is undefined at n = 0
--   - encoding: a randomized algorithm with coins → a Markov kernel from datasets to outputs; reason: the most general reading; the kernel's measurability is what makes the joint probability exist
--   - encoding: Σ = DDᵀ with D uniform on d×k matrices with orthonormal columns → covPrior d k, the law of G(GᵀG)⁻¹Gᵀ for a Gaussian d×k matrix G; reason: for k ≤ d this is the projector onto a Haar-uniform k-dimensional subspace, the paper's own remark after (5); it is a constructed law, not a hypothesis
--   - reading: "‖ℳ(X)‖₂ ≤ α" of Definition 2.2, written outside the probability → IsSampler: for every input and every coin; reason: the bound is a property of the algorithm; this is the strongest reading of the sampler the lemma produces
--   - encoding: α with no stated sign → α any real; IsSampler in the conclusion asserts 0 < α; reason: Definition 2.2 fixes α > 0, and the hypothesis forces it because the posterior of μ given X has no atoms
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Lemma 2.4, printed p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_UnknownCovDP_General_TestEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-- Lemma 2.4 (From mean estimation to sampling), printed p. 11, PDF p. 12. An accurate
`(1, c/n)`-DP mean estimator under `P_sub` yields a `(1, c/n)`-DP `(ck/n, α)`-sampler. -/
theorem lemma_2_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d k n : ℕ), 1 ≤ n → (n : ℝ) ≤ c * k → k ≤ d →
      ∀ (α : ℝ) (κ : Algorithm d n), IsMarkovKernel κ →
        PrivRobustStat.IsApproxDP (fun X => κ X) 1 (c / n) →
        3 / 4 ≤ experimentProb (Psub d k) n κ (fun μ _ _ => {y | ‖y - μ‖ ≤ α}) →
        ∃ κ' : Algorithm d n, IsMarkovKernel κ' ∧ IsSampler k (c * k / n) α κ' ∧
          PrivRobustStat.IsApproxDP (fun X => κ' X) 1 (c / n) := by sorry

end UnknownCovDP.General
