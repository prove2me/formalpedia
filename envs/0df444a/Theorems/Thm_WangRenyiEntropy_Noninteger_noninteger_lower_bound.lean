-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_noninteger_lower_bound
-- name    : WangRenyiEntropy.Noninteger.noninteger_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:14.846768+00:00
-- url     : https://prove2.me/theorems/671359e8-9aab-4c47-bf95-c343b884a088
-- title:
--   Theorem 3.2 — nonparametric sample lower bound
-- statement:
--   Fix any positive noninteger real $\alpha$. There are $c>0$, $d_0\ge2$ and $\varepsilon_0\in(0,1/16]$, all depending only on $\alpha$, such that for every $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$, every randomized estimator using $n$ iid samples with
--   $$n<c\frac{d^{\max\{1/\alpha,1\}}}{\varepsilon^{1/\alpha}\log d}$$
--   fails the uniform $2/3$ success requirement: some $d$-letter law has success probability strictly less than $2/3$. This supplies the first necessary term for every positive noninteger order, including $\alpha=1/2$ and all nonintegers above one.
--
--   Differences from the source:
--   - encoding: finite alphabet and nonnegative normalized real probability coordinates → Fin d with d ≥ 1 and the published IsLaw predicate, allowing zero coordinates; reason: relabeling preserves every finite nonempty alphabet and every probability law
--   - encoding: all estimators with success probability at least 2/3 → all maps from the discrete observed word to Borel probability measures on the real output, with their randomness integrated into success; reason: these maps are precisely randomized kernels on a countable discrete observation space; no dependence on the unknown law is permitted
--   - reading: sufficiently large d and sufficiently small ε, with constants depending only on α → positive constants and separate thresholds d₀(α) and ε₀(α) chosen before d and ε, uniformly for d ≥ d₀ and 0 < ε ≤ ε₀; reason: the proof on printed 10–12 supplies α-only alphabet thresholds and uses Lemma 1.3 in the complementary regime; printed 17 supplies a uniform upper budget
--   - encoding: sample-complexity lower bound → every integer budget strictly below the rate and every randomized estimator have a law with success strictly below 2/3; reason: operational necessity avoids a real infimum default or an attainment assumption; Fact 1.2 transfers the source Poisson argument to fixed iid samples
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 9 / PDF 11, Theorem 3.2

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WangRenyiEntropy.Noninteger

/-- Theorem 3.2, printed p.9 / PDF p.11, joint asymptotic reading. -/
theorem noninteger_lower_bound (α : ℝ) (hα : NonintegerOrder α) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 16 ∧
      ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ n : ℕ, (n : ℝ) < c * rateA α d ε →
      ∀ A : Estimator (Word d n), ∃ p : Law d,
        successProbability (multinomialLaw n p) A (entropy α p) ε < (2 / 3 : ℝ≥0∞) := by sorry

end WangRenyiEntropy.Noninteger
