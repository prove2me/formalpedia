-- Prove2me | Theorems.Thm_TamingMonster_Regret_iloveToConBandits_regret_le
-- name    : TamingMonster.Regret.iloveToConBandits_regret_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T09:04:02.319136+00:00
-- url     : https://prove2.me/theorems/2c7e1df6-7dec-427c-b169-b55aa21ea3ef
-- title:
--   Theorem 2 / Lemma 17 — ILOVETOCONBANDITS has regret $C_0(4Kd_{\tau_{m_0-1}}+\sqrt{8Kd_{\tau_{m(T)}}\tau_{m(T)}})+\sqrt{8T\ln(2/\delta)}$ w.p. $1-\delta$
-- statement:
--   Consider the i.i.d. contextual bandit problem with $K\ge1$ actions, a finite nonempty class $\Pi$ of measurable policies, and a distribution $\mathcal D$ of context/reward-vector pairs whose rewards lie in $[0,1]$. Run ILOVETOCONBANDITS (Algorithm 1) with failure probability $\delta\in(0,1)$ and an epoch schedule $0=\tau_0<\tau_1<\cdots$ satisfying $\tau_{m+1}\le 2\tau_m$ for $m\ge1$ and $m_0\ge2$, where in every epoch $Q_m$ is any solution of (OP) (chosen by a measurable rule of the history) and $\pi_t$ is any empirical maximizer. Let $\pi_\star$ be any policy maximizing $\mathcal R$ over $\Pi$. Then for every $T\in\mathbb N$, with probability at least $1-\delta$,
--   $$\sum_{t=1}^T\bigl(r_t(\pi_\star(x_t))-r_t(a_t)\bigr)\le C_0\Bigl(4Kd_{\tau_{m_0-1}}+\sqrt{8Kd_{\tau_{m(T)}}\tau_{m(T)}}\Bigr)+\sqrt{8T\ln(2/\delta)},$$
--   where $d_t=\ln(16t^2|\Pi|/\delta)$, $m(T)$ is the epoch containing round $T$, $C_0=4\psi+c_0$, $\psi=100$, $c_0=4\rho(1+\theta_1)$, $\theta_1=94.1$ and $\rho=\sup_{m\ge m_0}\sqrt{\tau_m/\tau_{m-1}}$.
--
--   This is the regret guarantee of the paper (Theorem 2), in the explicit form proved as Lemma 17. It gives regret $O(\sqrt{KT\ln(T|\Pi|/\delta)}+K\ln(T|\Pi|/\delta))$ for an algorithm that accesses the policy class only through an arg-max oracle.
--
--   **Formalization Note** The paper prints Theorem 2 with $O(\cdot)$; Lemma 17 gives the constant $C_0$, and this statement is Lemma 17. The data $(x_t,r_t)$ are an i.i.d. sequence with law $\mathcal D$; action draws use i.i.d. uniform numbers on $[0,1]$ independent of the data (inverse distribution function), so the action never looks at $r_t$. "(OP) can be solved whenever required" is a selection rule that returns an (OP) solution for every history of length $\tau_m$ (such rules exist by Theorem 3 of the paper). Conventions: $\mu_0=1/(2K)$; the hypothesis $m_0\ge2$ (i.e. $d_{\tau_1}/\tau_1>1/(4K)$, true e.g. for $\tau_1=1$) replaces the paper's "$\tau_1=O(1)$" and makes $d_{\tau_{m_0-1}}$ and $\rho$ finite; $\log$ in Lemma 17 is the natural logarithm, as in its proof. The regret is the empirical cumulative regret, not the pseudo-regret. The conclusion says that the failure event has (outer) probability at most $\delta$.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 5, Theorem 2; p. 21, Lemma 17 (explicit form); p. 22 (Theorem 2 follows from Lemma 17)

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

namespace TamingMonster.Regret

open MeasureTheory

/-- Theorem 2 (p. 5) in the explicit form of Lemma 17 (p. 21). Run ILOVETOCONBANDITS with
parameters `A` (policy class `Π`, failure probability `δ ∈ (0,1)`, epoch schedule
`0 = τ_0 < τ_1 < ⋯` with `τ_{m+1} ≤ 2τ_m` for `m ≥ 1` and `m₀ ≥ 2`, any empirical-argmax
tie-breaking rule and any (OP)-solution selection) on i.i.d. context/reward pairs
`(x_t, r_t) = Z t ∼ D` with rewards in `[0,1]`, the action draws driven by independent uniform
numbers `U t`. Let `π⋆` be any maximizer of `R` over `Π`. For every `T`, with probability at
least `1 − δ` the regret after `T` rounds is at most
`C₀(4K d_{τ_{m₀−1}} + √(8K d_{τ_{m(T)}} τ_{m(T)})) + √(8T ln(2/δ))`, `C₀ = 4ψ + c₀`. -/
theorem iloveToConBandits_regret_le {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty) (hPiMeas : ∀ π ∈ A.Pi, Measurable π)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (hτ2 : ∀ m, 1 ≤ m → A.τ (m + 1) ≤ 2 * A.τ m)
    (hm0 : 2 ≤ m0 A.Pi A.δ A.τ)
    (hpick : A.PickIsArgmax) (hsel : A.SelSolvesOP) (hrules : A.RulesMeasurable)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (hZmeas : ∀ t, Measurable (Z t)) (hUmeas : ∀ t, Measurable (U t))
    (hindep : ProbabilityTheory.iIndepFun (fun t ω => (Z t ω, U t ω)) P)
    (hZU : ∀ t, ProbabilityTheory.IndepFun (Z t) (U t) P)
    (hZlaw : ∀ t, P.map (Z t) = D)
    (hUlaw : ∀ t, P.map (U t) = volume.restrict (Set.Icc (0 : ℝ) 1))
    (πstar : A.Pi) (hstar : ∀ π : A.Pi, expReward D (π : X → Fin K) ≤ expReward D πstar)
    (T : ℕ) :
    P {ω | C0 A.Pi A.δ A.τ *
            (4 * (K : ℝ) * dT A.Pi A.δ (A.τ (m0 A.Pi A.δ A.τ - 1))
              + Real.sqrt (8 * (K : ℝ) * dT A.Pi A.δ (A.τ (epochOf A.τ T))
                  * (A.τ (epochOf A.τ T) : ℝ)))
          + Real.sqrt (8 * (T : ℝ) * Real.log (2 / A.δ))
        < A.cumRegret Z U (πstar : X → Fin K) ω T} ≤ ENNReal.ofReal A.δ := by sorry

end TamingMonster.Regret
