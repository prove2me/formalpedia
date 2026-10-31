-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_lemma_3_1
-- name    : UnbiasedTimeAvg.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:51.579124+00:00
-- url     : https://prove2.me/theorems/e842cbcd-1fa8-4fdf-b994-aeecd39a4001
-- title:
--   Lemma 3.1 — $\mathrm{Var}(f_{k,0})\le796\,\bar\nu(0)^2\sqrt{b'(k)-b(k)}/k^{3/2}+\mathrm{Var}(f_k)$
-- statement:
--   Assume the standing model and Assumption A1 with rate $\nu$. For $k\ge1$ and $b(k)\le b'(k)\le k/2$,
--   $$\mathrm{Var}(f_{k,0})\le\frac{796\,\bar\nu(0)^2}{k^{3/2}}\sqrt{b'(k)-b(k)}+\mathrm{Var}(f_k).$$
--
--   The variance of the base estimator $f_{k,0}$ of $\hat f_k$ exceeds that of the conventional $f_k$ by a lower-order term; this is the first ingredient of (3.11).
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: (2.5) E((f(X_{i,m}) − f(X_i))²) ≤ ν(i) → lower Lebesgue integral of the square compared with ν(i) in [0, ∞]; reason: the same expectation whether or not the square is integrable; changes no instance
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
--   - encoding: burn-ins b(k), b′(k) with b(k) ≤ b′(k) ≤ k/2 → two naturals `b ≤ b'` with `2 * b' ≤ k`; reason: the theorem is for one fixed k, so b(k) and b′(k) are two numbers; 2b′ ≤ k is b′ ≤ k/2
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Lemma 3.1, p.8; proof Appendix E, pp.26–27

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel
import Definitions.Def_UnbiasedTimeAvg_AssumptionA1
import Definitions.Def_UnbiasedTimeAvg_nuBar
import Definitions.Def_UnbiasedTimeAvg_timeAvgEstimator
import Definitions.Def_UnbiasedTimeAvg_levelEstimator

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Lemma 3.1 (variance of `f_{k,0}`).** Kahalé, arXiv:2209.09581v1, Lemma 3.1, p.8:
"For `k ≥ 1`, `Var(f_{k,0}) ≤ (796(ν̄(0))²/k^{3/2}) √(b′(k) − b(k)) + Var(f_k)`."

Assumption A1 is in force (§3.2, p.8: "This subsection supposes that Assumption A1 holds"), and
`b(k) ≤ b′(k) ≤ k/2`.

**Formalization Note.** `b`, `b'` are `b(k)`, `b′(k)` at the fixed `k`; `k^{3/2}` is the real
power `(k : ℝ) ^ (3/2 : ℝ)`. -/
theorem lemma_3_1
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) {ν : ℕ → ℝ} (hA1 : AssumptionA1 P U g f x₀ ν)
    (b b' k : ℕ) (hk : 1 ≤ k) (hbb' : b ≤ b') (hb' : 2 * b' ≤ k) :
    variance (levelEstimator g x₀ U f b' k 0) P
      ≤ 796 * (nuBar ν 0) ^ 2 / (k : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt ((b' : ℝ) - b)
        + variance (timeAvgEstimator g x₀ U f b k) P := by sorry

end UnbiasedTimeAvg
