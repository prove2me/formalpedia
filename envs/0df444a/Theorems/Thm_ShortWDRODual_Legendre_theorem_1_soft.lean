-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_theorem_1_soft
-- name    : ShortWDRODual.Legendre.theorem_1_soft
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:37:18.954982+00:00
-- url     : https://prove2.me/theorems/fc9b282e-70e7-47b0-a0af-3a955d8cedbb
-- title:
--   Theorem 1, first display, p. 3 — (−𝓛)*(−λ) = sup over γ ∈ Γ_ℙ̂ of 𝔼_γ[f(X) − λc(X̂, X)]
-- statement:
--   Assume Assumption 1 (as in Lemma 1) and let $\lambda>0$. Let $\Gamma_{\widehat{\mathbb P}}$ be the set of probability measures on $\mathcal X\times\mathcal X$ with first marginal $\widehat{\mathbb P}$. Then
--   $$(-\mathcal L)^*(-\lambda)=\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}\big[f(X)-\lambda c(\widehat X,X)\big].$$
--
--   Together with the identification of $(-\mathcal L)^*(-\lambda)$ with (P-soft), this is the first statement of Theorem 1: the soft-penalty problem equals a supremum over couplings with fixed first marginal, without any interchangeability assumption.
--
--   **Formalization Note** The supremum ranges over all of $\Gamma_{\widehat{\mathbb P}}$, including couplings of infinite expected cost; expectations use `extIntegral`, which gives $-\infty$ when both parts of the integrand are infinite.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Theorem 1, first display, p. 3 (PDF p. 3); proof p. 4 (PDF p. 4)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality

theorem theorem_1_soft {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    legendre (fun ρ => - robustLoss c f Phat ρ) (-lam) =
      ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam) := by sorry

end ShortWDRODual.Legendre
