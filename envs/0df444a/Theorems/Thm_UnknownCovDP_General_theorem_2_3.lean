-- Prove2me | Theorems.Thm_UnknownCovDP_General_theorem_2_3
-- name    : UnknownCovDP.General.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:42.858651+00:00
-- url     : https://prove2.me/theorems/a08db104-42ca-4e5c-a064-ee8f0bc92e9b
-- title:
--   Theorem 2.3 — lower bound for private sampling
-- statement:
--   There is a constant $c>0$ such that for all $d,k$, all $n\ge1$ and all $\lambda>0$: if $k\le cd$ and $n\log n\le ck$, then every $(\lambda,\alpha)$-sampler for $\mathcal P_{\mathrm{sub}}$ with sample complexity $n$ that is $(1,c/n)$-differentially private satisfies
--   $$\alpha\ge c\lambda\sqrt{d/k}.$$
--   This is the paper's main technical contribution: a private algorithm that correlates with the hidden subspace must output a long vector.
--
--   Differences from the source:
--   - encoding: n ∈ ℕ a sample size, with c/n in the statement → hypothesis 1 ≤ n; reason: c/n is undefined at n = 0
--   - encoding: a randomized algorithm with coins → a Markov kernel from datasets to outputs; reason: the most general reading; the kernel's measurability is what makes the joint probability exist
--   - encoding: Σ = DDᵀ with D uniform on d×k matrices with orthonormal columns → covPrior d k, the law of G(GᵀG)⁻¹Gᵀ for a Gaussian d×k matrix G; reason: for k ≤ d this is the projector onto a Haar-uniform k-dimensional subspace, the paper's own remark after (5); it is a constructed law, not a hypothesis
--   - generalization: (λ,α)-sampler with ‖ℳ(X)‖₂ ≤ α as a property of the algorithm → IsAESampler: the norm bound holds almost surely under Σ, X and the coins; reason: every IsSampler is an IsAESampler (IsSampler.toAE), so the statement specializes to the source's; the proof uses the bound only almost surely
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Theorem 2.3, printed p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_UnknownCovDP_General_TestEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-- Theorem 2.3 (Lower bound for private sampling), printed p. 11, PDF p. 12. There is `c > 0` such
that (`lam > 0` being part of `IsAESampler`) if `k ≤ cd` and `n log n ≤ ck`, every `(lam, α)`-sampler for `P_sub` with sample complexity `n`
that is `(1, c/n)`-DP has `α ≥ c lam √(d/k)`. -/
theorem theorem_2_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d k n : ℕ) (lam α : ℝ), 1 ≤ n → (k : ℝ) ≤ c * d →
      (n : ℝ) * Real.log n ≤ c * k →
      ∀ κ : Algorithm d n, IsMarkovKernel κ → IsAESampler k lam α κ →
        PrivRobustStat.IsApproxDP (fun X => κ X) 1 (c / n) →
        c * lam * Real.sqrt ((d : ℝ) / k) ≤ α := by sorry

end UnknownCovDP.General
