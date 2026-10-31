-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_eq_E_1
-- name    : UnbiasedTimeAvg.eq_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:50.727895+00:00
-- url     : https://prove2.me/theorems/64c2c39a-bf23-45a2-8243-44bc0cb1ec08
-- title:
--   (E.1) — $\mathrm{Std}(f_k)\le5\sqrt2\,\bar\nu(0)/\sqrt k$
-- statement:
--   Assume the standing model and Assumption A1 with rate $\nu$. For $k\ge1$ and a burn-in $b(k)\le k/2$, the conventional estimator $f_k=\frac1{k-b(k)}\sum_{i=b(k)}^{k-1}f(X_i)$ satisfies
--   $$\mathrm{Std}(f_k)\le\frac{5\sqrt2\,\bar\nu(0)}{\sqrt k}.\qquad(\mathrm{E}.1)$$
--
--   Equivalently $k\,\mathrm{Var}(f_k)\le50\,\bar\nu(0)^2$; this is the bound on the reference variance used in the proofs of Lemma 3.1 and Theorem 3.2.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: (2.5) E((f(X_{i,m}) − f(X_i))²) ≤ ν(i) → lower Lebesgue integral of the square compared with ν(i) in [0, ∞]; reason: the same expectation whether or not the square is integrable; changes no instance
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
--   - encoding: Std(·) → `Real.sqrt (variance · P)`; reason: Std is the square root of the variance; the variables are square-integrable, so the variance is the true one
--   - encoding: burn-in b(k) ≤ k/2 (standing, p.4) → a natural `b` with `2 * b ≤ k`; reason: the statement is for one fixed k
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), (E.1), p.27

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel
import Definitions.Def_UnbiasedTimeAvg_AssumptionA1
import Definitions.Def_UnbiasedTimeAvg_nuBar
import Definitions.Def_UnbiasedTimeAvg_timeAvgEstimator

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **(E.1): standard deviation of the conventional estimator `f_k`.** Kahalé,
arXiv:2209.09581v1, (E.1), p.27: "`Std(f_k) ≤ 5√2ν̄(0)/√k`, which is a consequence of Lemma 2.1."

It holds for every `k ≥ 1` under A1 and the standing `b(k) ≤ k/2` (p.4), so that `f_k`
averages `k − b(k) ≥ k/2` terms.

**Formalization Note.** `b` is `b(k)` at the fixed `k`; `Std` is `√variance`. -/
theorem eq_E_1
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) {ν : ℕ → ℝ} (hA1 : AssumptionA1 P U g f x₀ ν)
    (b k : ℕ) (hk : 1 ≤ k) (hb : 2 * b ≤ k) :
    Real.sqrt (variance (timeAvgEstimator g x₀ U f b k) P)
      ≤ 5 * Real.sqrt 2 * nuBar ν 0 / Real.sqrt k := by sorry

end UnbiasedTimeAvg
