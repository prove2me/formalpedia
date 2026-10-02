-- Prove2me | Theorems.Thm_TamingMonster_Regret_calV_le
-- name    : TamingMonster.Regret.calV_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:46:13.056515+00:00
-- url     : https://prove2.me/theorems/1282970b-0562-444e-ad7e-94b6e37320df
-- title:
--   Lemma 12 — on $\mathcal E$, $\mathcal V_t(\pi)\le 2K$ or $\theta_1K+\widehat{\mathrm{Reg}}_{\tau_m}(\pi)/(\theta_2\mu_m)$
-- statement:
--   Assume the event $\mathcal E$ holds for a run of ILOVETOCONBANDITS whose (OP)-selection returns solutions of (OP). Pick a round $t\ge1$ and a policy $\pi\in\Pi$, and let $m\le m(t)-1$ be an epoch achieving the maximum in the definition of $\mathcal V_t(\pi)=\max_{0\le m'\le m(t)-1}V(\widetilde Q_{m'},\pi,\mu_{m'})$. Then
--   $$\mathcal V_t(\pi)\le\begin{cases}2K&\text{if }\mu_m=1/(2K),\\[1mm]\theta_1K+\dfrac{\widehat{\mathrm{Reg}}_{\tau_m}(\pi)}{\theta_2\mu_m}&\text{if }\mu_m<1/(2K),\end{cases}$$
--   with $\theta_1=94.1$ and $\theta_2=\psi/6.4=15.625$.
--
--   The lemma turns the empirical variance constraint (3) of (OP) into a bound on the true variance: a policy whose variance is much larger than $K$ must have had a large estimated regret in an earlier epoch.
--
--   **Formalization Note** The statement is deterministic: it holds for every outcome in $\mathcal E$. Since $\mu_m\le1/(2K)$ always, the two cases are "$\mu_m=1/(2K)$" and "otherwise". When several epochs achieve the maximum, the bound holds for each of them. $m=0$ is allowed and falls in the first case ($\mu_0=1/(2K)$).
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 18, Lemma 12

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

namespace TamingMonster.Regret

open MeasureTheory

/-- Lemma 12, p. 18. On the event `ℰ`, for every round `t ≥ 1`, every policy `π ∈ Π`, and
every epoch `m ≤ m(t) − 1` achieving the maximum in the definition of `𝒱_t(π)`:
`𝒱_t(π) ≤ 2K` if `μ_m = 1/(2K)`, and `𝒱_t(π) ≤ θ₁K + R̂eg_{τ_m}(π)/(θ₂μ_m)` if
`μ_m < 1/(2K)`. -/
theorem calV_le {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ)
    (hsel : A.SelSolvesOP)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (hω : ω ∈ A.goodEvent D Z U)
    (t : ℕ) (ht : 1 ≤ t) (π : A.Pi) (m : ℕ) (hm : m < epochOf A.τ t)
    (hmax : A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) =
      Vpop (D.map Prod.fst) A.Pi (A.Qtilde Z U ω m) (π : X → Fin K) (muM A.Pi A.δ A.τ m)) :
    A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) ≤
      if muM A.Pi A.δ A.τ m = 1 / (2 * (K : ℝ)) then 2 * (K : ℝ)
      else theta1 * (K : ℝ)
        + estRegret A.Pi (A.history Z U ω (A.τ m)) (π : X → Fin K)
          / (theta2 * muM A.Pi A.δ A.τ m) := by sorry

end TamingMonster.Regret
