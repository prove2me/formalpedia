-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_theorem_1_IP_fixed
-- name    : ShortWDRODual.Legendre.theorem_1_IP_fixed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:28.842984+00:00
-- url     : https://prove2.me/theorems/055dde49-f653-4ed5-8163-1b19656eda31
-- title:
--   Theorem 1, third display, p. 3 — for λ > 0, φ_λ satisfies (IP) iff (−𝓛)*(−λ) = 𝒢(λ)
-- statement:
--   Assume Assumption 1 (as in Lemma 1) and let $\lambda>0$. Let $\phi_\lambda(\widehat x,x)=f(x)-\lambda c(\widehat x,x)$. Then $\phi_\lambda$ satisfies the interchangeability principle (IP) if and only if $\widehat x\mapsto\sup_x\phi_\lambda(\widehat x,x)$ is $\widehat{\mathbb P}$-measurable and
--   $$(-\mathcal L)^*(-\lambda)=\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x\in\mathcal X}\{f(x)-\lambda c(\widehat X,x)\}\Big].$$
--
--   This is the fixed-$\lambda$ form of the necessity and sufficiency of (IP) for the dual expression.
--
--   **Formalization Note** The measurability of the supremum function is stated explicitly on the right, because the paper's expectation on the right presupposes it (§2.1) and (IP) contains it; the paper's equivalence is read with this presupposition.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Theorem 1, third display, p. 3 (PDF p. 3); proof p. 5 (PDF p. 5)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality

theorem theorem_1_IP_fixed {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    IP Phat (phiLam c f lam) ↔
      (NullMeasurable (supFn (phiLam c f lam)) Phat ∧
        legendre (fun ρ => - robustLoss c f Phat ρ) (-lam) = dualG c f Phat lam) := by sorry

end ShortWDRODual.Legendre
