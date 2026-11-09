-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_optimal_sample_complexity
-- name    : WangRenyiEntropy.Noninteger.optimal_sample_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:35.411461+00:00
-- url     : https://prove2.me/theorems/5142a9a5-2c86-4cb8-8b30-d18a985435ba
-- title:
--   Theorem 1.1 — optimal sample complexity for every positive noninteger order
-- statement:
--   Fix any positive noninteger real order $\alpha$. There are constants $c_\alpha,C_\alpha>0$, an integer threshold $d_0(\alpha)\ge2$ and an accuracy threshold $\varepsilon_0(\alpha)\in(0,1/16]$, chosen independently of the alphabet, accuracy, unknown law and observations, such that for every $d\ge d_0(\alpha)$ and $0<\varepsilon\le\varepsilon_0(\alpha)$ the minimax iid sample complexity is
--   $$\Theta_\alpha\left(\frac{d^{\max\{1/\alpha,1\}}}{\varepsilon^{1/\alpha}\log d}+\frac{d^{|1-1/\alpha|}}{\varepsilon^2}\right).$$
--   More precisely, some integer $n\le\lceil C_\alpha(A_\alpha+B_\alpha)\rceil$ admits one randomized estimator whose probability of additive error at most $\varepsilon$ is at least $2/3$ for every law. Conversely, for every integer $n<c_\alpha(A_\alpha+B_\alpha)$ and every randomized estimator based on those $n$ ordered samples, some law has success probability strictly below $2/3$.
--
--   Both terms are retained, including at $\alpha=1/2$. For $0<\alpha\le1/2$, $B_\alpha/A_\alpha=(\log d/d)\varepsilon^{1/\alpha-2}\le1$, giving the source's equivalent first-regime simplification. For $1/2<\alpha<1$ and noninteger $\alpha>1$, both printed terms remain. This combines necessity over the full randomized class and sufficiency; no integer-order or Shannon sample-rate theorem is asserted.
--
--   Differences from the source:
--   - encoding: finite alphabet and nonnegative normalized real probability coordinates → Fin d with d ≥ 1 and the published IsLaw predicate, allowing zero coordinates; reason: relabeling preserves every finite nonempty alphabet and every probability law
--   - encoding: all estimators with success probability at least 2/3 → all maps from the discrete observed word to Borel probability measures on the real output, with their randomness integrated into success; reason: these maps are precisely randomized kernels on a countable discrete observation space; no dependence on the unknown law is permitted
--   - reading: sufficiently large d and sufficiently small ε, with constants depending only on α → positive constants and separate thresholds d₀(α) and ε₀(α) chosen before d and ε, uniformly for d ≥ d₀ and 0 < ε ≤ ε₀; reason: the proof on printed 10–12 supplies α-only alphabet thresholds and uses Lemma 1.3 in the complementary regime; printed 17 supplies a uniform upper budget
--   - encoding: Θα(A+B) samples are sufficient and necessary → an attainable integer upper budget with ceiling, and operational failure below cα(A+B); reason: states both directions and both terms without a real-valued-minimum or attainment convention; expected Poisson cost is converted to iid cost through Fact 1.2
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 2 / PDF 4, Theorem 1.1

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WangRenyiEntropy.Noninteger

/-- Theorem 1.1, printed p.2 / PDF p.4, full two-term rate and both directions.
Joint asymptotic reading: thresholds depend only on the fixed order α.
The upper estimator is chosen before p; the lower bound covers every randomized kernel. -/
theorem optimal_sample_complexity (α : ℝ) (hα : NonintegerOrder α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 16 ∧
      ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      (∃ n : ℕ, n ≤ Nat.ceil (C * (rateA α d ε + rateB α d ε)) ∧
        MultinomialAchievable α ε d n) ∧
      (∀ n : ℕ, (n : ℝ) < c * (rateA α d ε + rateB α d ε) →
        ∀ A : Estimator (Word d n), ∃ p : Law d,
          successProbability (multinomialLaw n p) A (entropy α p) ε < (2 / 3 : ℝ≥0∞)) := by sorry

end WangRenyiEntropy.Noninteger
