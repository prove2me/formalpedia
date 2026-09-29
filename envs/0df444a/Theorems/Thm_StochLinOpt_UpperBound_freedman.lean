-- Prove2me | Theorems.Thm_StochLinOpt_UpperBound_freedman
-- name    : StochLinOpt.UpperBound.freedman
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:31:28.612+00:00
-- url     : https://prove2.me/theorems/5ed1f808-8ff6-4afe-9032-49f105a32095
-- title:
--   Theorem 4 — Freedman's inequality for martingale differences
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_i)_{i\ge0}$. Let $X_1,\dots,X_T$ be real random variables such that for each $1\le i\le T$:
--
--   1. $X_i$ is $\mathcal F_{i+1}$-measurable, integrable, with $\mathbb E[X_i^2]<\infty$;
--   2. $\mathbb E[X_i\mid\mathcal F_i]=0$ almost surely (a martingale difference sequence);
--   3. $X_i\le b$ almost surely.
--
--   Let $V=\sum_{i=1}^{T}\mathbb E[X_i^2\mid\mathcal F_i]$ be the sum of conditional variances. Then for every $a>0$ and $v>0$,
--
--   $$\mathbb P\Big(\sum_{i=1}^{T}X_i\ge a\ \text{ and }\ V\le v\Big)\le\exp\Big(\frac{-a^2}{2v+2ab/3}\Big).$$
--
--   This Bernstein-type martingale inequality lets the step bound be large as long as the conditional variances are small; the paper uses it to prove Lemma 14.
--
--   **Formalization Note** The paper prints the variance sum up to $n$; this is a typo for $T$. The paper conditions on $X_1,\dots,X_{i-1}$; the statement uses a general filtration in which $X_i$ is known at time $i+1$ and conditioned on time $i$, which is Freedman's original form (Ann. Probab. 1975) and contains the natural filtration as a special case. Since $\mathbb E[X_i\mid\mathcal F_i]=0$, the conditional variance is $\mathbb E[X_i^2\mid\mathcal F_i]$. Square integrability is assumed so that this conditional expectation is not Lean's junk value $0$.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 6, Theorem 4 (Freedman [1975])

import Mathlib

open MeasureTheory

namespace StochLinOpt.UpperBound

theorem freedman {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[𝓕 (i + 1)] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | 𝓕 i] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by sorry

end StochLinOpt.UpperBound
