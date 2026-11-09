-- Prove2me | Theorems.Thm_UnknownCovDP_General_proposition_2_5
-- name    : UnknownCovDP.General.proposition_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:44.921222+00:00
-- url     : https://prove2.me/theorems/6d814ca7-a44e-44d0-b6f1-9d58803300c5
-- title:
--   Proposition 2.5 — Bayesian lower bound for private Gaussian mean estimation
-- statement:
--   There are absolute constants $c,C>0$ with the following property. Let $k\in\mathbb N$, $n\ge1$, $\varepsilon\le1$, $\delta\le c/n$ and $\rho\ge C\max(1,\sqrt k/n)$, and let $\mathcal A$ be an $(\varepsilon,\delta)$-differentially private algorithm from $n$ points of $\mathbb R^k$ to $\mathbb R^k$. Then
--   $$\Pr_{\mu\sim N(0,\rho^2I_k),\ X\sim N(\mu,I_k)^{\otimes n},\ \text{coins of }\mathcal A}\Bigl[\|\mathcal A(X)-\mu\|_2\ge\frac{ck}{n}\Bigr]\ge\frac13.$$
--   This is the isotropic bound that the paper imports (it cites the statement from [GLSUZ26] and calls it a folklore result); it is the only external statistical input of the reduction to sampling.
--
--   Differences from the source:
--   - reading: "Let k, n ∈ ℕ. There exist absolute constants c, C > 0" → ∃ c C before ∀ k n; reason: "absolute" means independent of k and n; this is the stronger reading
--   - encoding: n ∈ ℕ a sample size, with c/n in the statement → hypothesis 1 ≤ n; reason: c/n is undefined at n = 0
--   - encoding: a randomized algorithm with coins → a Markov kernel from datasets to outputs; reason: the most general reading; the kernel's measurability is what makes the joint probability exist
--   - generalization: δ ≤ c/n with the DP inequality additive in δ → IsApproxDP uses ENNReal.ofReal δ, so negative δ is replaced by zero; reason: this weakly enlarges the DP class and agrees with the source for δ ≥ 0; the enlarged class at δ < 0 satisfies the bound at δ = 0. In zero dimension there are no neighboring datasets, so the source class need not be empty, but the error threshold is zero and the conclusion is trivial
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Proposition 2.5, printed p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_UnknownCovDP_General_TestEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-- Proposition 2.5 (Folklore Result), printed p. 12, PDF p. 13. Absolute constants `c, C > 0`: for
every `(ε, δ)`-DP mechanism with `ε ≤ 1`, `δ ≤ c/n`, and every `ρ ≥ C max(1, √k/n)`,
`Pr_{μ∼N(0,ρ²I_k), X∼N(μ,I_k)^{⊗n}, coins}[‖𝒜(X) − μ‖₂ ≥ ck/n] ≥ 1/3`. -/
theorem proposition_2_5 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (k n : ℕ), 1 ≤ n → ∀ (ε δ ρ : ℝ), ε ≤ 1 → δ ≤ c / n →
      C * max 1 (Real.sqrt k / n) ≤ ρ →
      ∀ κ : Algorithm k n, IsMarkovKernel κ →
        PrivRobustStat.IsApproxDP (fun X => κ X) ε δ →
        (1 / 3 : ℝ≥0∞) ≤
          ∫⁻ μ, ∫⁻ X, κ X {y | c * k / n ≤ ‖y - μ‖} ∂(dataLaw n μ (1 : Mat k))
            ∂(multivariateGaussian (0 : Vec k) ((ρ ^ 2) • (1 : Mat k))) := by sorry

end UnknownCovDP.General
