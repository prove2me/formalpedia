-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_lemma_E_1
-- name    : UnbiasedTimeAvg.lemma_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:41.148984+00:00
-- url     : https://prove2.me/theorems/4053d448-103b-4619-a1f1-8ff649b33aef
-- title:
--   Lemma E.1 — $\mathrm{Std}(f_{k,0}-f_k)\le25\,\bar\nu(0)\sqrt{b'(k)-b(k)}/k$
-- statement:
--   Assume the standing model and Assumption A1 with rate $\nu$. Let $k\ge1$ and $b(k)\le b'(k)\le k/2$, let $f_k$ have burn-in $b(k)$ and $f_{k,0}$ burn-in $b'(k)$. Then
--   $$\mathrm{Std}\big(f_{k,0}-f_k\big)\le\frac{25\,\bar\nu(0)}{k}\sqrt{b'(k)-b(k)}.$$
--
--   Changing the burn-in from $b(k)$ to $b'(k)$ perturbs the estimator by $O(\sqrt{b'-b}/k)$ in standard deviation.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: (2.5) E((f(X_{i,m}) − f(X_i))²) ≤ ν(i) → lower Lebesgue integral of the square compared with ν(i) in [0, ∞]; reason: the same expectation whether or not the square is integrable; changes no instance
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
--   - encoding: Std(·) → `Real.sqrt (variance · P)`; reason: Std is the square root of the variance; the variables are square-integrable, so the variance is the true one
--   - encoding: burn-ins b(k), b′(k) with b(k) ≤ b′(k) ≤ k/2 → two naturals `b ≤ b'` with `2 * b' ≤ k`; reason: the theorem is for one fixed k, so b(k) and b′(k) are two numbers; 2b′ ≤ k is b′ ≤ k/2
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Lemma E.1, p.26; proof p.27

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel
import Definitions.Def_UnbiasedTimeAvg_AssumptionA1
import Definitions.Def_UnbiasedTimeAvg_nuBar
import Definitions.Def_UnbiasedTimeAvg_timeAvgEstimator
import Definitions.Def_UnbiasedTimeAvg_levelEstimator

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Lemma E.1 (the two burn-ins give close estimators).** Kahalé, arXiv:2209.09581v1,
Lemma E.1, p.26: "For `k ≥ 1`, `Std(f_{k,0} − f_k) ≤ (25ν̄(0)/k) √(b′(k) − b(k))`."

Here `f_k` has burn-in `b(k)` and `f_{k,0}` burn-in `b′(k)`, with `b(k) ≤ b′(k) ≤ k/2` (§3.2,
p.8), under Assumption A1 (in force throughout §3.2).

**Formalization Note.** `b`, `b'` are `b(k)`, `b′(k)` at the fixed `k`; `Std` is `√variance`;
`b′ − b` is computed in `ℝ`. -/
theorem lemma_E_1
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) {ν : ℕ → ℝ} (hA1 : AssumptionA1 P U g f x₀ ν)
    (b b' k : ℕ) (hk : 1 ≤ k) (hbb' : b ≤ b') (hb' : 2 * b' ≤ k) :
    Real.sqrt (variance (fun ω => levelEstimator g x₀ U f b' k 0 ω -
        timeAvgEstimator g x₀ U f b k ω) P)
      ≤ 25 * nuBar ν 0 / k * Real.sqrt ((b' : ℝ) - b) := by sorry

end UnbiasedTimeAvg
