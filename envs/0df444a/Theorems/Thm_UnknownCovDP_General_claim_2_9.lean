-- Prove2me | Theorems.Thm_UnknownCovDP_General_claim_2_9
-- name    : UnknownCovDP.General.claim_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:42.804551+00:00
-- url     : https://prove2.me/theorems/1dd35f52-f530-4f62-af75-5ffb8a6e50b3
-- title:
--   Claim 2.9 — $G$ has constant probability
-- statement:
--   There is a constant $c>0$ such that for every $C\ge48$ there is $K$ with the following property. Let $\Sigma\sim\mathcal P_{\mathrm{sub}}$, $X\sim N(0,\Sigma)^{\otimes n}$ and $y=\mathcal M(X)$ for a $(\lambda,\alpha)$-sampler $\mathcal M$ with sample complexity $n$. If $n\ge1$, $k\ge K$, $k\le cd$ and $n\le ck$, then
--   $$\Pr_{X,y,\Sigma}[G]\ge c,$$
--   where $G$ is built with the constants $C,\lambda,\alpha$. No privacy is assumed.
--
--   Differences from the source:
--   - reading: "for all sufficiently large k ≤ cd and n ≤ ck", with C "a sufficiently large constant" and the proof ending "for C ≥ 48 and c ≤ 1/24" → ∃ c, ∀ C ≥ 48, ∃ K, ∀ d k n λ α ℳ with K ≤ k, k ≤ c d, n ≤ c k; reason: the source leaves these objects to the surrounding proof; this is the stronger reading, with c independent of C
--   - encoding: n is a sample size, with division by n in the empirical covariance and test averages → hypothesis 1 ≤ n; reason: these sample averages are defined for positive sample size; the source does not use c/n in this result
--   - encoding: a randomized algorithm with coins → a Markov kernel from datasets to outputs; reason: the most general reading; the kernel's measurability is what makes the joint probability exist
--   - encoding: Σ = DDᵀ with D uniform on d×k matrices with orthonormal columns → covPrior d k, the law of G(GᵀG)⁻¹Gᵀ for a Gaussian d×k matrix G; reason: for k ≤ d this is the projector onto a Haar-uniform k-dimensional subspace, the paper's own remark after (5); it is a constructed law, not a hypothesis
--   - generalization: (λ,α)-sampler with ‖ℳ(X)‖₂ ≤ α as a property of the algorithm → IsAESampler: the norm bound holds almost surely under Σ, X and the coins; reason: every IsSampler is an IsAESampler (IsSampler.toAE), so the statement specializes to the source's; the proof uses the bound only almost surely
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Claim 2.9, printed p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_UnknownCovDP_General_TestEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-- Claim 2.9, printed p. 14, PDF p. 15. There is `c > 0` such that for every `C ≥ 48` and all
sufficiently large `k ≤ cd` and `n ≤ ck`, `Pr_{X,y,Σ}[G] ≥ c`, where `Σ ∼ P_sub`, `X ∼ N(0,Σ)^{⊗n}`
and `y = ℳ(X)` for a `(lam, α)`-sampler `ℳ` with sample complexity `n`. -/
theorem claim_2_9 :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ, 48 ≤ C → ∃ K : ℕ, ∀ (d k n : ℕ) (lam α : ℝ) (κ : Algorithm d n),
      IsMarkovKernel κ → 1 ≤ n → K ≤ k → (k : ℝ) ≤ c * d → (n : ℝ) ≤ c * k →
      IsAESampler k lam α κ →
      ENNReal.ofReal c ≤
        centeredProb (covPrior d k) n κ (fun S X => {y | EventG k C lam α S X y}) := by sorry

end UnknownCovDP.General
