-- Prove2me | Theorems.Thm_TamingMonster_Regret_variance_deviation
-- name    : TamingMonster.Regret.variance_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:34:40.158768+00:00
-- url     : https://prove2.me/theorems/bccedbbb-9b52-430e-8ae8-08a83e414a8c
-- title:
--   Lemma 10 — uniform deviation of $V(P,\pi,\mu_m)$ from $\widehat V_m(P,\pi,\mu_m)$
-- statement:
--   Let $x_1,x_2,\dots$ be i.i.d. contexts with law $\mathcal D_X$, let $\Pi$ be a finite nonempty class of measurable policies $X\to\{1,\dots,K\}$, let $0=\tau_0<\tau_1<\tau_2<\cdots$ be an epoch schedule, and fix numbers $\mu_m\in(0,1/K]$ for $m\ge1$. For every $\delta\in(0,1)$, with probability at least $1-\delta$ the following holds for all probability distributions $P$ over $\Pi$, all $\pi\in\Pi$ and all $m\ge1$:
--   $$V(P,\pi,\mu_m)\le 6.4\,\widehat V_m(P,\pi,\mu_m)+\frac{75(1-K\mu_m)\ln|\Pi|}{\mu_m^2\tau_m}+\frac{6.3\ln(2|\Pi|^2m^2/\delta)}{\mu_m\tau_m},$$
--   and in particular, if
--   $$\mu_m\ge\sqrt{\frac{\ln(2|\Pi|m^2/\delta)}{K\tau_m}},\qquad\tau_m\ge 4K\ln(2|\Pi|m^2/\delta),$$
--   then
--   $$V(P,\pi,\mu_m)\le 6.4\,\widehat V_m(P,\pi,\mu_m)+81.3K.$$
--   Here $V$ is the population and $\widehat V_m$ the empirical (over $x_1,\dots,x_{\tau_m}$) average of $1/P^{\mu_m}(\pi(x)\mid x)$.
--
--   The lemma supplies part (13) of the event $\mathcal E$: the empirical variance constraint of (OP) controls the true variance of the importance-weighted estimates. The bound holds simultaneously for all (not only finitely supported) distributions $P$.
--
--   **Formalization Note** The paper prints $\mu_m\in[0,1/K]$; at $\mu_m=0$ the bound involves division by $0$, so $\mu_m>0$ is assumed. $m$ ranges over $\{1,2,\dots\}$ as in the paper. The contexts are an i.i.d. sequence of measurable maps with law $\mathcal D_X$ (the lemma does not involve actions or rewards). The paper's proof is a sketch.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 15, Lemma 10 (with Eqs. (8)-(9), p. 14)

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

namespace TamingMonster.Regret

open MeasureTheory

/-- Lemma 10, p. 15. Contexts `x_1, x_2, …` are i.i.d. with law `ν = D_X`; the epoch schedule
`0 = τ_0 < τ_1 < ⋯` and the numbers `μ_m ∈ (0, 1/K]` (`m ≥ 1`) are fixed. For `δ ∈ (0,1)`, with
probability at least `1 − δ`, for all probability distributions `P` over `Π`, all `π ∈ Π` and all
`m ≥ 1`:
`V(P,π,μ_m) ≤ 6.4 V̂_m(P,π,μ_m) + 75(1 − Kμ_m) ln|Π|/(μ_m² τ_m) + 6.3 ln(2|Π|²m²/δ)/(μ_m τ_m)`,
and, if moreover `μ_m ≥ √(ln(2|Π|m²/δ)/(Kτ_m))` and `τ_m ≥ 4K ln(2|Π|m²/δ)`,
`V(P,π,μ_m) ≤ 6.4 V̂_m(P,π,μ_m) + 81.3K`. -/
theorem variance_deviation {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (hPiMeas : ∀ π ∈ Pi, Measurable π)
    (ν : Measure X) [IsProbabilityMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : ℕ → Ω → X) (hxmeas : ∀ t, Measurable (x t))
    (hxind : ProbabilityTheory.iIndepFun x P) (hxlaw : ∀ t, P.map (x t) = ν)
    (τ : ℕ → ℕ) (hτ0 : τ 0 = 0) (hτ : StrictMono τ)
    (μ : ℕ → ℝ) (hμ : ∀ m, 1 ≤ m → 0 < μ m ∧ μ m ≤ 1 / (K : ℝ))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    P {ω | ¬ ∀ Q : Pi → ℝ, (∀ π, 0 ≤ Q π) → ∑ π, Q π = 1 → ∀ π : Pi, ∀ m : ℕ, 1 ≤ m →
        (Vpop ν Pi Q (π : X → Fin K) (μ m) ≤
            64 / 10 * Vhat Pi Q (π : X → Fin K) (μ m) (fun i => x i ω) (τ m)
            + 75 * (1 - (K : ℝ) * μ m) * Real.log (Pi.card : ℝ) / (μ m ^ 2 * (τ m : ℝ))
            + 63 / 10 * Real.log (2 * (Pi.card : ℝ) ^ 2 * (m : ℝ) ^ 2 / δ) / (μ m * (τ m : ℝ)))
        ∧ (Real.sqrt (Real.log (2 * (Pi.card : ℝ) * (m : ℝ) ^ 2 / δ) / ((K : ℝ) * (τ m : ℝ)))
              ≤ μ m →
            4 * (K : ℝ) * Real.log (2 * (Pi.card : ℝ) * (m : ℝ) ^ 2 / δ) ≤ (τ m : ℝ) →
            Vpop ν Pi Q (π : X → Fin K) (μ m) ≤
              64 / 10 * Vhat Pi Q (π : X → Fin K) (μ m) (fun i => x i ω) (τ m)
              + 813 / 10 * (K : ℝ))} ≤ ENNReal.ofReal δ := by sorry

end TamingMonster.Regret
