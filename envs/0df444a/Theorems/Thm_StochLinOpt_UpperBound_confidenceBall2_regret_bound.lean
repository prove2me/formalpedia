-- Prove2me | Theorems.Thm_StochLinOpt_UpperBound_confidenceBall2_regret_bound
-- name    : StochLinOpt.UpperBound.confidenceBall2_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:33:49.442987+00:00
-- url     : https://prove2.me/theorems/e3e170dc-fa2b-465a-82e8-34cb849ec358
-- title:
--   Theorem 2 — ConfidenceBall₂ has regret $\le\sqrt{8nT\beta_T\ln(T+1)}$ for all $T$ with probability $\ge1-\delta$
-- statement:
--   **Model.** Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_t)$, where $\mathcal F_t$ is the information available before round $t=1,2,\dots$. The decision set $D\subseteq\mathbb R^n$ is compact, contains the standard basis vectors $e_1,\dots,e_n$, and lies in the cube $[-1,1]^n$ (the standard basis is a barycentric spanner of $D$). The unknown mean $\mu\in\mathbb R^n$ satisfies $|\mu^\top y|\le1$ for $y\in D$, and $x^*\in D$ minimises $\mu^\top y$ over $D$. On round $t$ the learner plays an $\mathcal F_t$-measurable decision $x_t$ and observes an $\mathcal F_{t+1}$-measurable loss $\ell_t\in[-1,1]$ with
--   $$\mathbb E[\ell_t\mid\mathcal F_t]=\mu^\top x_t\quad\text{and}\quad|\ell_t-\mu^\top x_t|\le1.$$
--   On every outcome, $(x_t)$ is a run of ConfidenceBall₂$(D,\delta)$ with losses $(\ell_t)$ (Algorithm 3.1), with $0<\delta<1$ and $n\le\big(\tfrac83\ln(1/\delta)\big)^2$.
--
--   **Claim.** With $\beta_T=\max\big(128n\ln T\ln(T^2/\delta),\ (\tfrac83\ln(T^2/\delta))^2\big)$ and $R_T=\sum_{t=1}^T(\mu^\top x_t-\mu^\top x^*)$,
--
--   $$\Pr\Big(\forall T\ge1,\ R_T\le\sqrt{8nT\beta_T\ln(T+1)}\Big)\ge1-\delta.$$
--
--   Since $\beta_T=O(n\log^2T)$, this is regret $O^*(n\sqrt T)$ uniformly over all horizons, with no dependence on the gap of the problem.
--
--   **Formalization Note** Three corrections of the printed statement, each forced by the paper's own proof:
--   1. $\ln(T+1)$ replaces the printed $\ln T$: the printed bound is false at $T=1$ ($n=1$, $D=[-1,1]$, $\mu>0$: the tie-break $x_1=1$ gives $R_1=2\mu>0$), and the proof, via Lemma 9, gives $\ln(T+1)$.
--   2. The hypothesis $n\le\beta_1=(\tfrac83\ln(1/\delta))^2$ is added: the proof of Theorem 5 uses $Z_1\le n<\beta_1$, which fails for $\delta$ near $1$.
--   3. The hypothesis $|\ell_t-\mu^\top x_t|\le1$ is added: Section 5.2 uses $|\eta_t|\le1$ while the paper's model only gives $|\eta_t|\le2$. It holds when costs lie in $[0,1]$.
--
--   Section 5 takes the barycentric spanner to be the standard basis without loss of generality. The filtration is general (containing the natural one), the conditional mean is imposed at the chosen decision only, and the event quantifies over all horizons $T\ge1$ at once.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 5, Theorem 2 (ConfidenceBall2 bullet); proof PDF p. 7

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix MeasureTheory

namespace StochLinOpt.UpperBound

theorem confidenceBall2_regret_bound {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℕ mΩ)
    (D : Set (Fin n → ℝ)) (hD_compact : IsCompact D)
    (hD_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hD_cube : ∀ y ∈ D, ∀ i, |y i| ≤ 1)
    (μ : Fin n → ℝ) (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ)
    (hx_meas : ∀ t : ℕ, 1 ≤ t → Measurable[𝓕 t] (x t))
    (hℓ_meas : ∀ t : ℕ, 1 ≤ t → Measurable[𝓕 (t + 1)] (ℓ t))
    (hℓ_bdd : ∀ t : ℕ, 1 ≤ t → ∀ ω, |ℓ t ω| ≤ 1)
    (hη_bdd : ∀ t : ℕ, 1 ≤ t → ∀ ω, |ℓ t ω - μ ⬝ᵥ x t ω| ≤ 1)
    (hmean : ∀ t : ℕ, 1 ≤ t → P[ℓ t | 𝓕 t] =ᵐ[P] fun ω => μ ⬝ᵥ x t ω)
    (hrun : ∀ ω, IsConfidenceBall2Run D δ (fun t => x t ω) (fun t => ℓ t ω))
    (hβ₁ : (n : ℝ) ≤ (8 / 3 * Real.log (1 / δ)) ^ 2)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y) :
    1 - δ ≤ P.real {ω | ∀ T : ℕ, 1 ≤ T →
      regret μ xstar (fun t => x t ω) T ≤
        Real.sqrt (8 * n * T * beta n δ T * Real.log (T + 1))} := by sorry

end StochLinOpt.UpperBound
