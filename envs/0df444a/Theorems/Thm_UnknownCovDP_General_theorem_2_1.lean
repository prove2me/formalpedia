-- Prove2me | Theorems.Thm_UnknownCovDP_General_theorem_2_1
-- name    : UnknownCovDP.General.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:38.16171+00:00
-- url     : https://prove2.me/theorems/2c8fe0a2-284f-4e85-94af-4561277a81d9
-- title:
--   Theorem 2.1 — lower bound for private mean estimation with unknown covariance
-- statement:
--   There is a constant $c>0$ such that for all $d,k$, all $n\ge1$ with $k\le cd$ and $n\log n\le ck$:
--
--   1. every $(1,c/n)$-differentially private algorithm $\mathcal A$ satisfies
--   $$\Pr_{(\mu,\Sigma)\sim\mathcal P_{\mathrm{sub}},\ X\sim N(\mu,\Sigma)^{\otimes n},\ \text{coins of }\mathcal A}\Bigl[\|\mathcal A(X)-\mu\|_2\ge\frac{c\sqrt{dk}}{n}\Bigr]\ge\frac14;$$
--   2. for all $\varepsilon\le1$ and $\delta\le c/n$,
--   $$\mathfrak R_{\varepsilon,\delta}(\mathcal P_{\mathrm{sub}},n)\ge\frac{c\sqrt{dk}}{n}.$$
--
--   When the covariance is known, the optimal error has no dependence on $d$ [DJYZZ24]; this theorem shows that not knowing the covariance costs a factor of order $\sqrt{d/k}$ up to polylogarithmic terms.
--
--   Differences from the source:
--   - encoding: n ∈ ℕ a sample size, with c/n in the statement → hypothesis 1 ≤ n; reason: c/n is undefined at n = 0
--   - encoding: a randomized algorithm with coins → a Markov kernel from datasets to outputs; reason: the most general reading; the kernel's measurability is what makes the joint probability exist
--   - encoding: Σ = DDᵀ with D uniform on d×k matrices with orthonormal columns → covPrior d k, the law of G(GᵀG)⁻¹Gᵀ for a Gaussian d×k matrix G; reason: for k ≤ d this is the projector onto a Haar-uniform k-dimensional subspace, the paper's own remark after (5); it is a constructed law, not a hypothesis
--   - reading: "ℜ_{ε,δ}(P_sub, n) = Ω(√(dk)/n)" → ℜ ≥ c√(dk)/n with the same c as the rest of the theorem; reason: the Ω is pinned by the theorem's own constant, the stronger reading; an existential c can always be shrunk to serve both clauses
--   - encoding: the Bayes risk as an infimum of nonnegative reals → bayesRisk valued in [0,∞], with sInf ∅ = +∞; reason: a real sInf of the empty set would be the junk value 0
--   - generalization: δ ≤ c/n with the DP inequality additive in δ → IsApproxDP uses ENNReal.ofReal δ, so negative δ is replaced by zero; reason: this weakly enlarges the DP class and agrees with the source for δ ≥ 0; the enlarged class at δ < 0 satisfies the bound at δ = 0. In zero dimension there are no neighboring datasets, so the source class need not be empty, but the error threshold is zero and the conclusion is trivial
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Theorem 2.1, printed p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_UnknownCovDP_General_TestEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-- Theorem 2.1 (Lower bound for private mean estimation with unknown covariance), printed p. 10,
PDF p. 11. There is `c > 0` such that for all `d, k, n` with `k ≤ cd` and `n log n ≤ ck`: every
`(1, c/n)`-DP algorithm has `Pr[‖𝒜(X) − μ‖₂ ≥ c√(dk)/n] ≥ 1/4` under `(μ,Σ) ∼ P_sub`,
`X ∼ N(μ,Σ)^{⊗n}`; and for all `ε ≤ 1`, `δ ≤ c/n`, `ℜ_{ε,δ}(P_sub, n) ≥ c√(dk)/n`. -/
theorem theorem_2_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d k n : ℕ), 1 ≤ n → (k : ℝ) ≤ c * d → (n : ℝ) * Real.log n ≤ c * k →
      (∀ κ : Algorithm d n, IsMarkovKernel κ →
        PrivRobustStat.IsApproxDP (fun X => κ X) 1 (c / n) →
        1 / 4 ≤ experimentProb (Psub d k) n κ
          (fun μ _ _ => {y | c * Real.sqrt ((d : ℝ) * k) / n ≤ ‖y - μ‖})) ∧
      (∀ ε δ : ℝ, ε ≤ 1 → δ ≤ c / n →
        ENNReal.ofReal (c * Real.sqrt ((d : ℝ) * k) / n) ≤ bayesRisk (Psub d k) n ε δ) := by sorry

end UnknownCovDP.General
