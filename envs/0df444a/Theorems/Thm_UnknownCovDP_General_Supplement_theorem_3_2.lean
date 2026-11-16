-- Prove2me | Theorems.Thm_UnknownCovDP_General_Supplement_theorem_3_2
-- name    : UnknownCovDP.General.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:46:54.028198+00:00
-- url     : https://prove2.me/theorems/6eed1872-d896-4a32-b1d1-94f3f9aa83c3
-- title:
--   Theorem 3.2 — lower bound for private mean estimation under unknown diagonal covariance
-- statement:
--   Let $d,n\in\mathbb N$ with $n\ge1$. Under the prior $\mathcal P_{\mathrm{diag}}(d)$, the mean is $\mu\sim N(0,d^2I_d)$ and, independently, $\Sigma=\mathrm{Diag}(\sigma_1^2,\dots,\sigma_d^2)$ with the $\sigma_i^2$ i.i.d. $\mathrm{inv}\chi^2(1,1)$. Given $(\mu,\Sigma)$, the dataset is $X\sim N(\mu,\Sigma)^{\otimes n}$. For a prior $\mathcal P$, $\mathfrak R_{\varepsilon,\delta}(\mathcal P,n)$ is the Bayes risk: the infimum of the $\alpha\ge0$ such that some $(\varepsilon,\delta)$-differentially private algorithm $\mathcal A$ has $\Pr[\|\mathcal A(X)-\mu\|_2\le\alpha]\ge 3/4$.
--
--   There is an absolute constant $c>0$ such that, whenever $n\log n\le c\sqrt d$:
--
--   1. every $(1,c/n)$-differentially private algorithm $\mathcal A$ satisfies
--   $$\Pr_{(\mu,\Sigma)\sim\mathcal P_{\mathrm{diag}},\ X\sim N(\mu,\Sigma)^{\otimes n},\ \text{coins of }\mathcal A}\Bigl[\|\mathcal A(X)-\mu\|_2\ge \frac{c\,d^{3/2}}{n^2\log d}\Bigr]\ge\frac14;$$
--   2. for all $\varepsilon\le1$ and $\delta\le c/n$,
--   $$\mathfrak R_{\varepsilon,\delta}(\mathcal P_{\mathrm{diag}},n)\ge \frac{c\,d^{3/2}}{n^2\log d}.$$
--
--   When the covariance is diagonal but unknown, private mean estimation in the regime $n\log n\le\sqrt d$ thus costs error of order $d^{3/2}/n^2$ up to a logarithm. This matches the third term of the known upper bound, so that term is necessary.
--
--   Differences from the source:
--   - encoding: d, n ∈ ℕ with c/n in the DP parameter → 1 ≤ n; reason: c/n is undefined at n = 0; the base mission's accepted encoding (Theorem 2.1)
--   - reading: That is, ℜ_{ε,δ}(P_diag, n) = Ω̃(d^{3/2}/n²) → ENNReal.ofReal (c d^{3/2}/(n² log d)) ≤ bayesRisk (Pdiag d) n ε δ with the theorem's own c; reason: the Ω̃ is pinned to the threshold the proof on p. 17 delivers; this is stronger than Ω̃ and a separate conclusion from the probability clause
--   - encoding: c d^{3/2}/(n² log d), undefined at d = 1 where log d = 0 → real division with x/0 = 0, so both clauses are trivial at d ≤ 1; reason: Lean convention; no hypothesis d ≥ 2 is added and no instance with d ≥ 2 changes
--   - encoding: a randomized algorithm 𝒜 and probability over the prior, the data and the coins of 𝒜 → a Markov kernel κ and the base experimentProb (iterated lintegral); reason: the base mission's model; same instances
--   - encoding: (1, c/n)-DP → PrivRobustStat.IsApproxDP (fun X => κ X) 1 (c / n) with replace-one neighbours; reason: the published definition used by the base mission; adds no condition
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Theorem 3.2, printed p. 16 (PDF p. 17); prior eq. (9) and Definition 3.1, same page; Bayes risk Definition 1.2, printed p. 2 (PDF p. 3)

import Mathlib
import Definitions.Def_UnknownCovDP_General_Supplement_DiagPrior

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General.Supplement

/-- Theorem 3.2, printed p. 16, PDF p. 17. There is `c > 0` such that for all `d, n` with
`n log n ≤ c√d`: every `(1, c/n)`-DP algorithm has
`Pr[‖𝒜(X) − μ‖₂ ≥ c d^{3/2}/(n² log d)] ≥ 1/4` under `(μ,Σ) ∼ P_diag`, `X ∼ N(μ,Σ)^{⊗n}`; and for all
`ε ≤ 1`, `δ ≤ c/n`, `ℜ_{ε,δ}(P_diag, n) ≥ c d^{3/2}/(n² log d)` (the `Ω̃` of the "That is" clause,
pinned to the same threshold). `n ≥ 1` because `c/n` is undefined at `n = 0`. At `d = 1`,
`log d = 0` and the threshold is `0` in Lean. -/
theorem theorem_3_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d n : ℕ), 1 ≤ n → (n : ℝ) * Real.log n ≤ c * Real.sqrt d →
      (∀ κ : Algorithm d n, IsMarkovKernel κ →
        PrivRobustStat.IsApproxDP (fun X => κ X) 1 (c / n) →
        1 / 4 ≤ experimentProb (Pdiag d) n κ
          (fun μ _ _ => {y | c * (d : ℝ) ^ ((3 : ℝ) / 2) / ((n : ℝ) ^ 2 * Real.log d) ≤ ‖y - μ‖})) ∧
      (∀ ε δ : ℝ, ε ≤ 1 → δ ≤ c / n →
        ENNReal.ofReal (c * (d : ℝ) ^ ((3 : ℝ) / 2) / ((n : ℝ) ^ 2 * Real.log d)) ≤
          bayesRisk (Pdiag d) n ε δ) := by sorry

end UnknownCovDP.General.Supplement
