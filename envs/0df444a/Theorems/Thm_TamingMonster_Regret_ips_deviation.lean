-- Prove2me | Theorems.Thm_TamingMonster_Regret_ips_deviation
-- name    : TamingMonster.Regret.ips_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:40:45.124704+00:00
-- url     : https://prove2.me/theorems/dba768ce-cc87-482a-8450-ffdac20a280a
-- title:
--   Lemma 11 — deviation of the IPS estimates $\widehat{\mathcal R}_t(\pi)$
-- statement:
--   Run ILOVETOCONBANDITS on i.i.d. context/reward pairs $(x_t,r_t)\sim\mathcal D$ with rewards in $[0,1]$, where the action of each round is drawn from $\widetilde Q_{m-1}^{\mu_{m-1}}(\cdot\mid x_t)$ with fresh independent randomness. For every $\delta'\in(0,1)$ and every choice of numbers $\lambda_{m-1}\in(0,\mu_{m-1}]$, $m\ge1$, with probability at least $1-\delta'$,
--   $$\bigl|\widehat{\mathcal R}_t(\pi)-\mathcal R(\pi)\bigr|\le\mathcal V_t(\pi)\lambda_{m-1}+\frac{\ln(4t^2|\Pi|/\delta')}{t\lambda_{m-1}}$$
--   for all policies $\pi\in\Pi$, all epochs $m\ge1$ and all rounds $t$ in epoch $m$ (that is, $\tau_{m-1}<t\le\tau_m$).
--
--   Here $\widehat{\mathcal R}_t$ is the inverse propensity estimate computed from the algorithm's own history $H_t$, and $\mathcal V_t(\pi)$ is the largest true variance $V(\widetilde Q_m,\pi,\mu_m)$ over the epochs $m<m(t)$. The lemma supplies part (14) of the event $\mathcal E$.
--
--   **Formalization Note** The paper allows $\lambda_{m-1}=0$, where the bound is $+\infty$; since $x/0=0$ in Lean, $\lambda_{m-1}>0$ is assumed. $\delta'$ is a variable separate from the algorithm's input $\delta$ (which still defines $\mu_m$). The run is the one defined in the Algorithm file: $(x_t,r_t)$ i.i.d. with law $\mathcal D$, the uniform numbers $u_t$ i.i.d. uniform on $[0,1]$ and independent of the pairs, and the tie-breaking and (OP)-selection rules measurable, with the selection returning (OP) solutions.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 16, Lemma 11 (with Eqs. (10)-(11))

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

namespace TamingMonster.Regret

open MeasureTheory

/-- Lemma 11, p. 16. Run ILOVETOCONBANDITS (parameters `A`) on i.i.d. context/reward pairs
`Z t = (x_t, r_t) ∼ D` and independent uniform numbers `U t` driving the action draws. For any
`δ' ∈ (0,1)` and any choice of `λ_{m−1} ∈ (0, μ_{m−1}]` (`m ≥ 1`), with probability at least
`1 − δ'`, `|R̂_t(π) − R(π)| ≤ 𝒱_t(π)λ_{m−1} + ln(4t²|Π|/δ')/(tλ_{m−1})` for all `π ∈ Π`, all
epochs `m ≥ 1` and all rounds `t` in epoch `m` (`τ_{m−1} < t ≤ τ_m`). -/
theorem ips_deviation {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty) (hPiMeas : ∀ π ∈ A.Pi, Measurable π)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
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
    (δ' : ℝ) (hδ'0 : 0 < δ') (hδ'1 : δ' < 1)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 < lam j ∧ lam j ≤ muM A.Pi A.δ A.τ j) :
    P {ω | ∃ π : A.Pi, ∃ m : ℕ, 1 ≤ m ∧ ∃ t : ℕ, A.τ (m - 1) < t ∧ t ≤ A.τ m ∧
        A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) * lam (m - 1)
          + Real.log (4 * (t : ℝ) ^ 2 * (A.Pi.card : ℝ) / δ') / ((t : ℝ) * lam (m - 1))
        < |ipsEst (A.history Z U ω t) (π : X → Fin K) - expReward D (π : X → Fin K)|}
      ≤ ENNReal.ofReal δ' := by sorry

end TamingMonster.Regret
