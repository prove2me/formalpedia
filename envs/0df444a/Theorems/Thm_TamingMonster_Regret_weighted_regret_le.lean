-- Prove2me | Theorems.Thm_TamingMonster_Regret_weighted_regret_le
-- name    : TamingMonster.Regret.weighted_regret_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:53:35.397597+00:00
-- url     : https://prove2.me/theorems/0a80be19-112a-4313-a2eb-493f7d27f6c3
-- title:
--   Lemma 14 — on $\mathcal E$, $\sum_\pi\widetilde Q_{m-1}(\pi)\mathrm{Reg}(\pi)\le(4\psi+c_0)K\mu_{m-1}$
-- statement:
--   Assume the event $\mathcal E$ holds for a run of ILOVETOCONBANDITS (empirical-maximizer tie-breaking, (OP)-selection returning solutions of (OP)), with rewards in $[0,1]$, the schedule satisfying $\tau_{m+1}\le2\tau_m$ for $m\ge1$, and $m_0\ge2$. Then for every epoch $m\ge1$,
--   $$\sum_{\pi\in\Pi}\widetilde Q_{m-1}(\pi)\,\mathrm{Reg}(\pi)\le(4\psi+c_0)K\mu_{m-1},$$
--   where $\widetilde Q_{m-1}$ is the distribution over policies from which the algorithm samples during epoch $m$, $\psi=100$ and $c_0=4\rho(1+\theta_1)$ is the constant of Lemma 13.
--
--   This is the per-round "low regret guarantee" of the sampling distribution; summing it over rounds gives the regret bound.
--
--   **Formalization Note** Deterministic on $\mathcal E$. For $m=1$, $\widetilde Q_0$ is the point mass at the arbitrary initial policy $\pi_0$ and $\mu_0=1/(2K)$.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 20, Lemma 14

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

namespace TamingMonster.Regret

open MeasureTheory

/-- Lemma 14, p. 20. On the event `ℰ`, for every epoch `m ≥ 1`,
`∑_{π ∈ Π} Q̃_{m−1}(π) Reg(π) ≤ (4ψ + c₀)Kμ_{m−1}`, where `Q̃_{m−1}` are the completed weights
the algorithm samples from during epoch `m`. -/
theorem weighted_regret_le {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty) (hPiMeas : ∀ π ∈ A.Pi, Measurable π)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (hτ2 : ∀ m, 1 ≤ m → A.τ (m + 1) ≤ 2 * A.τ m)
    (hm0 : 2 ≤ m0 A.Pi A.δ A.τ)
    (hpick : A.PickIsArgmax) (hsel : A.SelSolvesOP)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ∀ a, z.2 a ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (hω : ω ∈ A.goodEvent D Z U)
    (m : ℕ) (hm : 1 ≤ m) :
    ∑ π : A.Pi, A.Qtilde Z U ω (m - 1) π * polRegret A.Pi D (π : X → Fin K) ≤
      (4 * psi + c0 A.Pi A.δ A.τ) * (K : ℝ) * muM A.Pi A.δ A.τ (m - 1) := by sorry

end TamingMonster.Regret
