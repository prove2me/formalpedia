-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_parametric_lower_bound
-- name    : WangRenyiEntropy.Noninteger.parametric_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:22.728201+00:00
-- url     : https://prove2.me/theorems/16f94a62-f8e2-484a-b6ec-31cba9b97e9b
-- title:
--   Lemma 1.3 — accuracy-dependent sample lower bound
-- statement:
--   Fix a real $\alpha>0$, $\alpha\ne1$, including positive integer orders. There are $c>0$, $d_0\ge2$ and $\varepsilon_0\in(0,1]$, depending only on $\alpha$, such that for all $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$, every randomized estimator using an integer number $n$ of iid samples with
--   $$n<c\frac{d^{|1-1/\alpha|}}{\varepsilon^2}$$
--   has some $d$-letter law on which its probability of additive error at most $\varepsilon$ is strictly below $2/3$.
--
--   This is the second necessary rate term, including the regime where accuracy rather than the first term controls the sample cost.
--
--   Differences from the source:
--   - encoding: finite alphabet and nonnegative normalized real probability coordinates → Fin d with d ≥ 1 and the published IsLaw predicate, allowing zero coordinates; reason: relabeling preserves every finite nonempty alphabet and every probability law
--   - encoding: all estimators with success probability at least 2/3 → all maps from the discrete observed word to Borel probability measures on the real output, with their randomness integrated into success; reason: these maps are precisely randomized kernels on a countable discrete observation space; no dependence on the unknown law is permitted
--   - reading: sufficiently large d and sufficiently small ε, with constants depending only on α → positive constants and separate thresholds d₀(α) and ε₀(α) chosen before d and ε, uniformly for d ≥ d₀ and 0 < ε ≤ ε₀; reason: Lemma 1.3 itself states sufficiently large d and sufficiently small ε at fixed α on printed 5 / PDF 7; the separate thresholds make this joint asymptotic reading explicit, and ε₀ ≤ 1 is a harmless threshold normalization
--   - encoding: sample-complexity lower bound → every integer budget strictly below the rate and every randomized estimator have a law with success strictly below 2/3; reason: operational necessity avoids a real infimum default or an attainment assumption; Fact 1.2 transfers the source Poisson argument to fixed iid samples
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 5 / PDF 7, Lemma 1.3

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WangRenyiEntropy.Noninteger

/-- Lemma 1.3, printed p.5 / PDF p.7. Integer orders are included.
The constants and both thresholds precede d and ε. -/
theorem parametric_lower_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ n : ℕ, (n : ℝ) < c * rateB α d ε →
      ∀ A : Estimator (Word d n), ∃ p : Law d,
        successProbability (multinomialLaw n p) A (entropy α p) ε < (2 / 3 : ℝ≥0∞) := by sorry

end WangRenyiEntropy.Noninteger
