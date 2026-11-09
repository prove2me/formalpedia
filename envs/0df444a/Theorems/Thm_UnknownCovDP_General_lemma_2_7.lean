-- Prove2me | Theorems.Thm_UnknownCovDP_General_lemma_2_7
-- name    : UnknownCovDP.General.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:08.595413+00:00
-- url     : https://prove2.me/theorems/c3741389-d852-4a55-9c19-343e4e2518fb
-- title:
--   Lemma 2.7 — IN case lower bound
-- statement:
--   There is $c_0>0$ such that for every $c\in(0,c_0]$ the following holds. Let $\Sigma\sim\mathcal P_{\mathrm{sub}}$, $X\sim N(0,\Sigma)^{\otimes n}$ and $y=\mathcal M(X)$ for a $(\lambda,\alpha)$-sampler $\mathcal M$ with sample complexity $n\ge1$. If $n\le ck$ and $\alpha\le c\lambda\sqrt{d/k}$, then for $i$ uniform in $[n]$,
--   $$\Pr_{X,y,\Sigma,i}\Bigl[T_{\Sigma,y}(x_i)\ge\frac{k}{4n}\Bigr]\ge\frac cn.$$
--   A short sampler output has to correlate with its own data points. No privacy is assumed.
--
--   Differences from the source:
--   - reading: "Let c > 0 be a sufficiently small constant" → ∃ c₀ > 0, ∀ c ∈ (0, c₀]; reason: the literal meaning of "sufficiently small"
--   - reading: X, y, Σ left implicit in the lemma → Σ ∼ covPrior d k, X ∼ N(0,Σ)^{⊗n}, y from the kernel of a sampler; reason: the objects fixed at the start of §2.2 and in the proof
--   - encoding: n ∈ ℕ a sample size, with c/n in the statement → hypothesis 1 ≤ n; reason: c/n is undefined at n = 0
--   - encoding: a randomized algorithm with coins → a Markov kernel from datasets to outputs; reason: the most general reading; the kernel's measurability is what makes the joint probability exist
--   - encoding: Σ = DDᵀ with D uniform on d×k matrices with orthonormal columns → covPrior d k, the law of G(GᵀG)⁻¹Gᵀ for a Gaussian d×k matrix G; reason: for k ≤ d this is the projector onto a Haar-uniform k-dimensional subspace, the paper's own remark after (5); it is a constructed law, not a hypothesis
--   - generalization: (λ,α)-sampler with ‖ℳ(X)‖₂ ≤ α as a property of the algorithm → IsAESampler: the norm bound holds almost surely under Σ, X and the coins; reason: every IsSampler is an IsAESampler (IsSampler.toAE), so the statement specializes to the source's; the proof uses the bound only almost surely
--   - encoding: i ∼ [n] uniform, jointly with X, y, Σ → (1/n) ∑ i of the probabilities; reason: i is independent of X, y and Σ
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Lemma 2.7, printed p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_UnknownCovDP_General_TestEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-- Lemma 2.7 (IN case lower bound), printed p. 13, PDF p. 14. For every sufficiently small `c > 0`:
if `n ≤ ck`, `α ≤ c lam √(d/k)` and `ℳ` is a `(lam, α)`-sampler with sample complexity `n`, then for
`i` uniform in `[n]`, `Pr_{X,y,Σ,i}[T_{Σ,y}(x_i) ≥ k/(4n)] ≥ c/n`. -/
theorem lemma_2_7 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∀ (d k n : ℕ) (lam α : ℝ) (κ : Algorithm d n), IsMarkovKernel κ → 1 ≤ n →
        (n : ℝ) ≤ c * k → α ≤ c * lam * Real.sqrt ((d : ℝ) / k) →
        IsAESampler k lam α κ →
        ENNReal.ofReal (c / n) ≤
          (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, centeredProb (covPrior d k) n κ
            (fun S X => {y | (k : ℝ) / (4 * n) ≤ testStat S y (X i)}) := by sorry

end UnknownCovDP.General
