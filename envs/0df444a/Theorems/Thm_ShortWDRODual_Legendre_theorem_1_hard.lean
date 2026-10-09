-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_theorem_1_hard
-- name    : ShortWDRODual.Legendre.theorem_1_hard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:03.414822+00:00
-- url     : https://prove2.me/theorems/fb1cb182-18e3-42d6-8e33-e8dc5c34143e
-- title:
--   Theorem 1, second display, p. 3 — 𝓛(ρ) = min over λ ≥ 0 of λρ + sup over γ ∈ Γ_ℙ̂ of 𝔼_γ[f(X) − λc(X̂, X)], ρ > 0
-- statement:
--   Assume Assumption 1 (as in Lemma 1) and let $\rho>0$. Then
--   $$\mathcal L(\rho)=\min_{\lambda\ge0}\Big\{\lambda\rho+\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}\big[f(X)-\lambda c(\widehat X,X)\big]\Big\},$$
--   and the minimum is attained: some $\lambda\ge0$ achieves $\mathcal L(\rho)$, and no $\lambda\ge0$ gives a smaller value. Here $0\cdot\infty=\infty$, so for $\lambda=0$ the integrand is $-\infty$ where $c(\widehat X,X)=\infty$.
--
--   This is strong duality for Wasserstein distributionally robust optimization in its general form, with no assumption beyond Assumption 1; the supremum over couplings has not yet been interchanged with the expectation.
--
--   **Formalization Note** "min" is `IsLeast`: $\mathcal L(\rho)$ belongs to the set of values $\{\lambda\rho+\dots:\lambda\ge0\}$ and is a lower bound for it. Values are in `EReal`; both sides may be $+\infty$. Expectations use `extIntegral` ($\infty-\infty=-\infty$).
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Theorem 1, second display, p. 3 (PDF p. 3); proof pp. 4–5 (PDF pp. 4–5)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality

theorem theorem_1_hard {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (ρ : ℝ) (hρ : 0 < ρ) :
    IsLeast
      {y : EReal | ∃ lam : ℝ, 0 ≤ lam ∧
        y = ((lam * ρ : ℝ) : EReal) + ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam)}
      (robustLoss c f Phat ρ) := by sorry

end ShortWDRODual.Legendre
