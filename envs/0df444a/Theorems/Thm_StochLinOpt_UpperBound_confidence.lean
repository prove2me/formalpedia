-- Prove2me | Theorems.Thm_StochLinOpt_UpperBound_confidence
-- name    : StochLinOpt.UpperBound.confidence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:33:16.50499+00:00
-- url     : https://prove2.me/theorems/867a0888-26a6-41d3-84fd-3c2450f55542
-- title:
--   Theorem 5 (Confidence) — $\Pr(\forall t,\ \mu\in B^2_t)\ge1-\delta$
-- statement:
--   **Model.** As in Lemma 14: a probability space with a filtration $(\mathcal F_t)$; a compact decision set $D\subseteq[-1,1]^n$ containing $e_1,\dots,e_n$; an unknown mean $\mu$ with $|\mu^\top y|\le1$ on $D$; $0<\delta<1$; $\mathcal F_t$-measurable decisions $x_t$; $\mathcal F_{t+1}$-measurable losses $\ell_t\in[-1,1]$ with $\mathbb E[\ell_t\mid\mathcal F_t]=\mu^\top x_t$ and $|\ell_t-\mu^\top x_t|\le1$; and $(x_t)$ a run of ConfidenceBall₂$(D,\delta)$ on every outcome. Assume in addition $n\le\beta_1=\big(\tfrac83\ln(1/\delta)\big)^2$. Then
--
--   $$\Pr\big(\forall t\ge1,\ \mu\in B^2_t\big)\ge1-\delta.$$
--
--   The confidence ellipsoids of ConfidenceBall₂ contain the true mean at all times simultaneously with probability at least $1-\delta$; this is the probabilistic half of the upper bound.
--
--   **Formalization Note** The paper states "Let $\delta>0$"; $\delta<1$ is added, as Algorithm 3.1 and Lemma 14 assume. The hypothesis $n\le\beta_1$ is added: the proof asserts "$Z_1\le n<\beta_1$ by the definition of $\beta_1$", which fails for $\delta$ close to $1$, and $Z_1=\|\mu\|^2$ is deterministic. The hypothesis $|\ell_t-\mu^\top x_t|\le1$ is added because the proof uses $|\eta_\tau|\le1$ while the model gives only $|\eta_t|\le2$. The Section 5 coordinates are without loss of generality. The event is a single event over all $t\ge1$.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 6, Theorem 5 (ConfidenceBall2 bullet); proof PDF p. 10, Section 5.2

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix MeasureTheory

namespace StochLinOpt.UpperBound

theorem confidence {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
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
    (hβ₁ : (n : ℝ) ≤ (8 / 3 * Real.log (1 / δ)) ^ 2) :
    1 - δ ≤ P.real {ω | ∀ t : ℕ, 1 ≤ t →
      μ ∈ confBall δ (fun s => x s ω) (fun s => ℓ s ω) t} := by sorry

end StochLinOpt.UpperBound
