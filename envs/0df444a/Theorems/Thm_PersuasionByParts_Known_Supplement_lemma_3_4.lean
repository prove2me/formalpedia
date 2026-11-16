-- Prove2me | Theorems.Thm_PersuasionByParts_Known_Supplement_lemma_3_4
-- name    : PersuasionByParts.Known.Supplement.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:48:55.18445+00:00
-- url     : https://prove2.me/theorems/0aa6bd3b-c53d-4b98-b2e4-124a472880a6
-- title:
--   Lemma 3.4 — Conditional product bound $\mathbb E[\mathbf 1_E R]\ge e^{-2^r/r}\mathbb P(E)^{1+1/r}$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and let $W_1,\dots,W_n$ be independent random variables with values in $[0,1/2]$ such that
--
--   $$\sum_{i=1}^n\mathbb E[W_i]\ \le\ \tfrac12 .$$
--
--   Set $R:=\prod_{i=1}^n(1-W_i)$. Then for every real $r>0$ and every event $E\in\mathcal F$,
--
--   $$\mathbb E[\mathbf 1_E\,R]\ \ge\ e^{-2^r/r}\,\mathbb P(E)^{1+1/r}.$$
--
--   The exponent of $e$ is $-(2^r)/r$. A bound linear in $\mathbb P(E)$ with a constant independent of $n$ is impossible, so this almost-linear bound is the form used to compare the universal experiment with each single-cutoff experiment in the proof of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: random variables W_1, …, W_n ∈ [0, 1/2] → measurable real functions W i on a probability space (Ω, μ) with W i ω ∈ [0, 1/2] for every ω; reason: a version taking values in [0, 1/2] almost surely can be modified on a null set without changing independence, the expectations or either side of the inequality
--   - encoding: independent → iIndepFun W μ (mutual independence); reason: the standard meaning of independence of a finite family
--   - encoding: every event E, 𝔼[1_E R], ℙ(E)^{1+1/r} → every measurable set A, the set integral ∫ ω in A, ∏ i, (1 − W i ω) ∂μ, (μ.real A) ^ (1 + 1/r) (rpow); reason: events are measurable sets; R is bounded in [0, 1], so the set integral is 𝔼[1_E R]
--   - generalization: n random variables (in the application n ≥ 1 sources) → any n : ℕ, including n = 0; reason: for n = 0 the product R is 1 and the claim is ℙ(E) ≥ e^{−2^r/r} ℙ(E)^{1+1/r}; every instance with n ≥ 1 is a special case
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 14 / PDF p. 15, Lemma 3.4 (Conditional product bound); the factor e^{−2^r/r} checked against the rendered page

import Mathlib

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Supplement

/-- Lemma 3.4, printed p. 14 / PDF p. 15: independent `W i ∈ [0, 1/2]` with
`∑ E[W i] ≤ 1/2`, `R = ∏ (1 - W i)`; for every `r > 0` and every event `A`,
`E[1_A R] ≥ exp(-2^r / r) · P(A)^(1 + 1/r)`. Any `n`, including `n = 0`. -/
theorem lemma_3_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (W : Fin n → Ω → ℝ) (hW_meas : ∀ i, Measurable (W i))
    (hW_range : ∀ i ω, W i ω ∈ Icc (0 : ℝ) (1 / 2))
    (hW_indep : iIndepFun W μ)
    (hW_sum : ∑ i, ∫ ω, W i ω ∂μ ≤ 1 / 2)
    (r : ℝ) (hr : 0 < r) (A : Set Ω) (hA : MeasurableSet A) :
    ∫ ω in A, (∏ i, (1 - W i ω)) ∂μ ≥
      Real.exp (-((2 : ℝ) ^ r) / r) * (μ.real A) ^ (1 + 1 / r) := by sorry

end PersuasionByParts.Known.Supplement
