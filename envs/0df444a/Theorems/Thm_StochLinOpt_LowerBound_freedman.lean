-- Prove2me | Theorems.Thm_StochLinOpt_LowerBound_freedman
-- name    : StochLinOpt.LowerBound.freedman
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:34:40.276834+00:00
-- url     : https://prove2.me/theorems/8848461d-6727-41b2-a5ae-3dadff699037
-- title:
--   Theorem 4 (Freedman) — Bernstein-type tail bound for martingales
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $(\mathcal F_i)_{i\ge0}$, and let $X_1,\dots,X_T$ be real random variables such that for each $i$:
--
--   1. $X_i$ is $\mathcal F_i$-measurable, integrable and square-integrable;
--   2. $\mathbb E[X_i\mid\mathcal F_{i-1}]=0$ almost surely (a martingale difference sequence);
--   3. $X_i\le b$ almost surely, for a constant $b$.
--
--   Let $V=\sum_{i=1}^T\mathbb E[X_i^2\mid\mathcal F_{i-1}]$ be the sum of conditional variances. Then for every $a>0$ and $v>0$,
--   $$P\Big(\sum_{i=1}^T X_i\ge a\ \text{ and }\ V\le v\Big)\le\exp\Big(\frac{-a^2}{2v+2ab/3}\Big).$$
--
--   This is Freedman's Bernstein-type inequality (Freedman 1975; McDiarmid 1998, Theorem 3.15). In Section 6.1 it is applied to the stopped bias martingale and its negative to show that the bias rarely leaves $[-1/2,1/2]$ while the accumulated conditional variance is small.
--
--   **Formalization Note** The paper writes the variance sum as $\sum_{i=1}^n$ and conditions on $X_1,\dots,X_{i-1}$; here the sum runs to $T$ (the paper's $n$ is a typo) and the conditioning is on a general filtration to which the $X_i$ are adapted, which contains the natural one and is the form used in Section 6.1 (the filtration of histories $\mathcal H_t$). Because $\mathbb E[X_i\mid\mathcal F_{i-1}]=0$, the conditional variance equals the conditional second moment. Square-integrability is assumed so that Lean's conditional expectation of $X_i^2$ is not the junk value $0$; it holds in every application here (bounded steps).
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 6, Theorem 4 (Freedman)

import Mathlib

open MeasureTheory

namespace StochLinOpt.LowerBound

theorem freedman {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[ℱ i] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | ℱ (i - 1)] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by sorry

end StochLinOpt.LowerBound
