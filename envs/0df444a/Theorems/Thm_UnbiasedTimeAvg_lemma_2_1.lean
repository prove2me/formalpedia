-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_lemma_2_1
-- name    : UnbiasedTimeAvg.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:36.470446+00:00
-- url     : https://prove2.me/theorems/860d0907-96d1-4343-bfe3-ad6655c30cb9
-- title:
--   Lemma 2.1 — $\mathrm{Std}$ of a $k$-term time average is at most $5\bar\nu(0)/\sqrt k$
-- statement:
--   Assume the standing model and Assumption A1 with rate $\nu$. Then for every $h\ge0$ and $k>0$,
--   $$\mathrm{Std}\Big(\frac1k\sum_{i=h}^{h+k-1}f(X_i)\Big)\le\frac{5\,\bar\nu(0)}{\sqrt k}.\qquad(2.13)$$
--
--   The bound is uniform in the starting time $h$ and of the optimal order $1/\sqrt k$; it controls the variance of every time-average estimator used later.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: (2.5) E((f(X_{i,m}) − f(X_i))²) ≤ ν(i) → lower Lebesgue integral of the square compared with ν(i) in [0, ∞]; reason: the same expectation whether or not the square is integrable; changes no instance
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
--   - encoding: Std(·) → `Real.sqrt (variance · P)`; reason: Std is the square root of the variance; the variables are square-integrable, so the variance is the true one
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Lemma 2.1, (2.13), p.6; proof Appendix B, pp.21–23

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel
import Definitions.Def_UnbiasedTimeAvg_AssumptionA1
import Definitions.Def_UnbiasedTimeAvg_nuBar

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Lemma 2.1 (standard deviation of a time average).** Kahalé, arXiv:2209.09581v1, Lemma 2.1,
(2.13), p.6: "Suppose that A1 holds. Then, for `h ≥ 0` and `k > 0`,
`Std((1/k) Σ_{i=h}^{h+k−1} f(X_i)) ≤ 5ν̄(0)/√k`."

**Formalization Note.** `Std` is the square root of `ProbabilityTheory.variance`; the average is
square-integrable by the standing assumption of `ChainModel`, so the variance is the true one. -/
theorem lemma_2_1
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) {ν : ℕ → ℝ} (hA1 : AssumptionA1 P U g f x₀ ν)
    (h k : ℕ) (hk : 0 < k) :
    Real.sqrt (variance (fun ω => (1 / (k : ℝ)) *
        ∑ i ∈ Finset.Ico h (h + k), f (coupledChain g x₀ U i 0 ω)) P)
      ≤ 5 * nuBar ν 0 / Real.sqrt k := by sorry

end UnbiasedTimeAvg
