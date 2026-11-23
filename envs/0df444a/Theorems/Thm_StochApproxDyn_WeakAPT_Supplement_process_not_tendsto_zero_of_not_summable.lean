-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_process_not_tendsto_zero_of_not_summable
-- name    : StochApproxDyn.WeakAPT.Supplement.process_not_tendsto_zero_of_not_summable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:18:59.075686+00:00
-- url     : https://prove2.me/theorems/9e65af4a-94b0-4150-84ee-7fbfd65b3975
-- title:
--   Lemma 9.7 — a process with bounded increments and excited squares does not converge to 0 when Σγₙ² = ∞
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $(\mathcal F_n)$. Let $(S_n)$ be a real stochastic process, $S_n=S_0+\sum_{i=1}^nX_i$, where $S_0$ is $\mathcal F_0$-measurable, $X_n$ is $\mathcal F_n$-measurable and $|X_n|\le C$. Let $(\gamma_n)$ be such that $\sum_i\gamma_i^2=\infty$. Assume there exist $a_1>0$ and an integer $N_0$ such that for all $n\ge N_0$,
--   $$E(S_{n+1}^2-S_n^2\mid\mathcal F_n)\ge a_1\gamma_{n+1}^2.$$
--   Then
--
--   $$P\Big(\lim_{n\to\infty}S_n=0\Big)=0.$$
--
--   This lemma covers the case $\sum\gamma_n^2=\infty$ of Theorem 9.1. Unlike Lemma 9.6 it does not require $S_n\ge0$.
--
--   **Formalization Note** Since $S_n$ is $\mathcal F_n$-measurable, $E(S_{n+1}^2-S_n^2\mid\mathcal F_n)=2S_nE(X_{n+1}\mid\mathcal F_n)+E(X_{n+1}^2\mid\mathcal F_n)$, and the hypothesis is written in that form. $\sum\gamma_i^2=\infty$ is non-summability of $(\gamma_{n+1}^2)$.
--
--   Differences from the source:
--   - reading: "$\{S_n\}$ a stochastic process … $X_n$ is $\mathcal F_n$ measurable" → $S_0$ is also $\mathcal F_0$-measurable; reason: the hypothesis given $\mathcal F_n$ treats $S_n$ as known.
--   - encoding: $E(S_{n+1}^2-S_n^2\mid\mathcal F_n)$ → $2S_nE(X_{n+1}\mid\mathcal F_n)+E(X_{n+1}^2\mid\mathcal F_n)$; reason: equal for $\mathcal F_n$-measurable $S_n$, and needs no integrability of $S_n$.
--   - encoding: $\sum_i\gamma_i^2=\infty$ → `¬ Summable (fun n => γ (n+1)^2)`; reason: equivalent for nonnegative terms.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 58, Lemma 9.7

import Mathlib

open MeasureTheory Filter

namespace StochApproxDyn.WeakAPT.Supplement

/-- Lemma 9.7 (Benaïm 1999, p. 58). Let `{S_n}` be a stochastic process,
`S_n = S_0 + ∑_{i=1}^n X_i`, where `X_n` is `ℱ_n`-measurable (and `S_0` is `ℱ_0`-measurable) and
`|X_n| ≤ C`. Let `{γ_n}` be such that `∑_i γ_i² = ∞`. Assume there exist `a₁ > 0` and an integer
`N₀` such that for all `n ≥ N₀`, `E(S_{n+1}² − S_n² | ℱ_n) ≥ a₁ γ_{n+1}²`. Then
`P(lim_{n → ∞} S_n = 0) = 0`.

The process is not assumed nonnegative. The conditional expectation of
`S_{n+1}² − S_n² = 2 S_n X_{n+1} + X_{n+1}²` is written as
`2 S_n E(X_{n+1} | ℱ_n) + E(X_{n+1}² | ℱ_n)`, its value for the `ℱ_n`-measurable `S_n`. -/
theorem process_not_tendsto_zero_of_not_summable {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (S X : ℕ → Ω → ℝ) (hS0 : StronglyMeasurable[ℱ 0] (S 0))
    (hX : ∀ n : ℕ, StronglyMeasurable[ℱ (n + 1)] (X (n + 1)))
    (hSX : ∀ n ω, S (n + 1) ω = S n ω + X (n + 1) ω)
    (C : ℝ) (hC : ∀ n ω, |X (n + 1) ω| ≤ C)
    (γ : ℕ → ℝ) (hγ : ¬ Summable (fun n : ℕ => γ (n + 1) ^ 2))
    (a₁ : ℝ) (ha₁ : 0 < a₁) (N₀ : ℕ)
    (h_iii : ∀ n, N₀ ≤ n → ∀ᵐ ω ∂P,
      a₁ * γ (n + 1) ^ 2 ≤ 2 * S n ω * (P[X (n + 1) | ℱ n]) ω +
        (P[fun ω => X (n + 1) ω ^ 2 | ℱ n]) ω) :
    P {ω | Tendsto (fun n => S n ω) atTop (nhds 0)} = 0 := by sorry

end StochApproxDyn.WeakAPT.Supplement
