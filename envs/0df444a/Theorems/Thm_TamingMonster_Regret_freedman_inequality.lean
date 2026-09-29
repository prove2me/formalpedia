-- Prove2me | Theorems.Thm_TamingMonster_Regret_freedman_inequality
-- name    : TamingMonster.Regret.freedman_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:30:12.770986+00:00
-- url     : https://prove2.me/theorems/1ffe9a6c-52be-49fd-a3da-c94e455b2d4e
-- title:
--   Lemma 9 — Freedman's inequality
-- statement:
--   Let $X_1,\dots,X_T$ be real random variables on a probability space. Suppose that for every $t\in\{1,\dots,T\}$, $X_t\le R$ almost surely and $\mathbb E[X_t\mid X_1,\dots,X_{t-1}]=0$. Put
--   $$S=\sum_{t=1}^T X_t,\qquad V=\sum_{t=1}^T\mathbb E[X_t^2\mid X_1,\dots,X_{t-1}].$$
--   Then for every $\delta\in(0,1)$ and every $\lambda\in(0,1/R]$, with probability at least $1-\delta$,
--   $$S\le (e-2)\lambda V+\frac{\ln(1/\delta)}{\lambda}.$$
--
--   This is the martingale concentration inequality behind the deviation bound for the inverse propensity estimates (Lemma 11); its strength is that it scales with the conditional variance $V$ rather than with the range $R$.
--
--   **Formalization Note** The conditioning is on the natural σ-algebra $\sigma(X_1,\dots,X_{t-1})$ (trivial for $t=1$). The paper allows $\lambda=0$, where the bound is $+\infty$; Lean's convention $x/0=0$ would make that case false, so $\lambda>0$ and $R>0$ are assumed. The variables are assumed measurable with $X_t$ and $X_t^2$ integrable (implicit in the paper; otherwise the conditional expectations are not defined). The conclusion is stated as "the failure event has (outer) probability at most $\delta$".
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 14, Lemma 9 (quoted from Beygelzimer et al. 2011)

import Mathlib

namespace TamingMonster.Regret

open MeasureTheory

/-- Lemma 9 (Freedman's inequality, as quoted from Beygelzimer et al. 2011), p. 14.
`Xs 1, …, Xs T` are real random variables with `X_t ≤ R` and `E[X_t | X_1, …, X_{t−1}] = 0`;
`S = ∑_{t=1}^T X_t` and `V = ∑_{t=1}^T E[X_t² | X_1, …, X_{t−1}]`. For `δ ∈ (0,1)` and
`λ ∈ (0, 1/R]`, the event `S > (e − 2)λV + ln(1/δ)/λ` has probability at most `δ`.
The conditioning σ-algebra for round `t` is `σ(X_1, …, X_{t−1})` (trivial for `t = 1`). -/
theorem freedman_inequality {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Xs : ℕ → Ω → ℝ) (T : ℕ) (R : ℝ) (hR : 0 < R)
    (hmeas : ∀ t, Measurable (Xs t))
    (hint : ∀ t, Integrable (Xs t) P)
    (hint2 : ∀ t, Integrable (fun ω => Xs t ω ^ 2) P)
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, Xs t ω ≤ R)
    (hmart : ∀ t ∈ Finset.Icc 1 T,
      condExp (⨆ i ∈ Finset.Icc 1 (t - 1), MeasurableSpace.comap (Xs i) inferInstance) P (Xs t)
        =ᵐ[P] 0)
    (δ lam : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R) :
    P {ω | (Real.exp 1 - 2) * lam *
            (∑ t ∈ Finset.Icc 1 T,
              condExp (⨆ i ∈ Finset.Icc 1 (t - 1), MeasurableSpace.comap (Xs i) inferInstance) P
                (fun ω' => Xs t ω' ^ 2) ω)
          + Real.log (1 / δ) / lam
        < ∑ t ∈ Finset.Icc 1 T, Xs t ω} ≤ ENNReal.ofReal δ := by sorry

end TamingMonster.Regret
