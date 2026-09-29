-- Prove2me | Theorems.Thm_TamingMonster_Regret_regret_estRegret_compare
-- name    : TamingMonster.Regret.regret_estRegret_compare
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:49:06.679384+00:00
-- url     : https://prove2.me/theorems/d5ab7fd9-f764-4a37-84a1-0b64011345f1
-- title:
--   Lemma 13 — on $\mathcal E$, $\mathrm{Reg}(\pi)$ and $\widehat{\mathrm{Reg}}_t(\pi)$ are within a factor 2 up to $c_0K\mu_m$
-- statement:
--   Assume the event $\mathcal E$ holds for a run of ILOVETOCONBANDITS (empirical-maximizer tie-breaking, (OP)-selection returning solutions of (OP)), with the schedule satisfying $\tau_{m+1}\le2\tau_m$ for $m\ge1$ and $m_0\ge2$. Let $c_0=4\rho(1+\theta_1)$. For all epochs $m\ge m_0$, all rounds $t\ge t_0$ in epoch $m$ (so $\tau_{m-1}<t\le\tau_m$), and all policies $\pi\in\Pi$,
--   $$\mathrm{Reg}(\pi)\le 2\,\widehat{\mathrm{Reg}}_t(\pi)+c_0K\mu_m,\qquad \widehat{\mathrm{Reg}}_t(\pi)\le 2\,\mathrm{Reg}(\pi)+c_0K\mu_m.$$
--
--   The lemma is the core of the regret analysis: the estimated regrets, which the algorithm can compute, track the true regrets, so the low-estimated-regret constraint (2) of (OP) implies low true regret.
--
--   **Formalization Note** The statement is deterministic on $\mathcal E$. The hypothesis $m_0\ge2$ makes $\rho$ finite: at $m_0=1$ the paper's $\rho$ contains $\tau_1/\tau_0=+\infty$ (and the lemma is empty there), while the real supremum in Lean would take a junk value. $\rho$ is not replaced by its upper bound $\sqrt2$.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 18, Lemma 13 (with t_0 defined just before it, and ρ, m_0 on p. 17)

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

namespace TamingMonster.Regret

open MeasureTheory

/-- Lemma 13, p. 18. On the event `ℰ`, with `c₀ = 4ρ(1 + θ₁)`: for all epochs `m ≥ m₀`, all
rounds `t ≥ t₀` in epoch `m` (`τ_{m−1} < t ≤ τ_m`) and all policies `π ∈ Π`,
`Reg(π) ≤ 2 R̂eg_t(π) + c₀Kμ_m` and `R̂eg_t(π) ≤ 2 Reg(π) + c₀Kμ_m`. -/
theorem regret_estRegret_compare {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (A : AlgoParams X K)
    (hPi : A.Pi.Nonempty)
    (hδ0 : 0 < A.δ) (hδ1 : A.δ < 1)
    (hτ0 : A.τ 0 = 0) (hτ : StrictMono A.τ) (hτ2 : ∀ m, 1 ≤ m → A.τ (m + 1) ≤ 2 * A.τ m)
    (hm0 : 2 ≤ m0 A.Pi A.δ A.τ)
    (hpick : A.PickIsArgmax) (hsel : A.SelSolvesOP)
    (D : Measure (X × (Fin K → ℝ))) [IsProbabilityMeasure D]
    {Ω : Type*} (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ)
    (ω : Ω) (hω : ω ∈ A.goodEvent D Z U)
    (m : ℕ) (hm : m0 A.Pi A.δ A.τ ≤ m) (t : ℕ) (ht1 : A.τ (m - 1) < t) (ht2 : t ≤ A.τ m)
    (ht0 : t0 A.Pi A.δ ≤ t) (π : A.Pi) :
    polRegret A.Pi D (π : X → Fin K) ≤
        2 * estRegret A.Pi (A.history Z U ω t) (π : X → Fin K)
          + c0 A.Pi A.δ A.τ * (K : ℝ) * muM A.Pi A.δ A.τ m ∧
      estRegret A.Pi (A.history Z U ω t) (π : X → Fin K) ≤
        2 * polRegret A.Pi D (π : X → Fin K)
          + c0 A.Pi A.δ A.τ * (K : ℝ) * muM A.Pi A.δ A.τ m := by sorry

end TamingMonster.Regret
