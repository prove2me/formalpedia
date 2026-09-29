-- Prove2me | Theorems.Thm_StochLinOpt_UpperBound_martingale_sum_le_half_beta
-- name    : StochLinOpt.UpperBound.martingale_sum_le_half_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:32:41.405295+00:00
-- url     : https://prove2.me/theorems/a44ac43d-937f-4604-b413-98bd53d3ca47
-- title:
--   Lemma 14 — $\Pr(\forall t,\ \sum_{\tau<t}M_\tau\le\beta_t/2)\ge1-\delta$
-- statement:
--   **Model.** Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_t)$, where $\mathcal F_t$ is the information available before round $t$. The decision set $D\subseteq[-1,1]^n$ is compact and contains $e_1,\dots,e_n$; the unknown mean $\mu\in\mathbb R^n$ satisfies $|\mu^\top y|\le1$ on $D$; and $0<\delta<1$. The decisions $x_t$ are $\mathcal F_t$-measurable, the losses $\ell_t\in[-1,1]$ are $\mathcal F_{t+1}$-measurable, $\mathbb E[\ell_t\mid\mathcal F_t]=\mu^\top x_t$ almost surely, the noise satisfies $|\ell_t-\mu^\top x_t|\le1$, and on every outcome $(x_t)$ is a run of ConfidenceBall₂$(D,\delta)$ with losses $(\ell_t)$.
--
--   With $M_t=2\eta_tE_t\,x_t^\top(\hat\mu_t-\mu)/(1+w_t^2)$,
--
--   $$\Pr\Big(\forall t\ge1,\ \sum_{\tau=1}^{t-1}M_\tau\le\frac{\beta_t}{2}\Big)\ge1-\delta.$$
--
--   This is the concentration step of the confidence argument, obtained from Freedman's inequality and a union bound over $t$.
--
--   **Formalization Note** The event is a single event quantified over all $t\ge1$. The hypothesis $|\ell_t-\mu^\top x_t|\le1$ is added: the paper's proof uses $|\eta_\tau|\le1$ (PDF p. 10), but its model only gives $|\eta_t|\le2$; the hypothesis holds when costs lie in $[0,1]$. A general filtration makes the statement more general than the natural filtration of the losses; the proof uses only the listed properties. The conditional-mean hypothesis is imposed only at the chosen decision $x_t$, which is weaker than the paper's "for all $x\in D$". The Section 5 coordinates (spanner equal to the standard basis) are without loss of generality.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 9, Lemma 14; proof PDF p. 10, Section 5.2.1

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix MeasureTheory

namespace StochLinOpt.UpperBound

theorem martingale_sum_le_half_beta {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
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
    (hrun : ∀ ω, IsConfidenceBall2Run D δ (fun t => x t ω) (fun t => ℓ t ω)) :
    1 - δ ≤ P.real {ω | ∀ t : ℕ, 1 ≤ t →
      ∑ τ ∈ Finset.Ico 1 t, mIncrement δ μ (fun s => x s ω) (fun s => ℓ s ω) τ ≤
        beta n δ t / 2} := by sorry

end StochLinOpt.UpperBound
