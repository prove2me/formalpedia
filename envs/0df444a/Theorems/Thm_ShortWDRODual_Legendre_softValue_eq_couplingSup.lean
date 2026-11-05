-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_softValue_eq_couplingSup
-- name    : ShortWDRODual.Legendre.softValue_eq_couplingSup
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T11:58:03.881033+00:00
-- url     : https://prove2.me/theorems/41c00eb5-38a3-4abc-a110-029108d6cc5a
-- title:
--   Proof of Theorem 1, p. 4 — (P-soft) = sup over γ ∈ Γ_ℙ̂ of 𝔼_γ[f(X) − λc(X̂, X)] for λ ≥ 0
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space, $f:\mathcal X\to\mathbb R$ measurable with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$, and $c:\mathcal X\times\mathcal X\to[0,\infty]$ a measurable cost with $c(x,x)=0$ (Assumption 1). Let $\bar{\mathcal P}$ be the set of probability measures $\mathbb P$ with $\mathcal K_c(\widehat{\mathbb P},\mathbb P)<\infty$, and $\Gamma_{\widehat{\mathbb P}}$ the probability measures on $\mathcal X\times\mathcal X$ with first marginal $\widehat{\mathbb P}$. Then for every $\lambda\ge0$,
--   $$\sup_{\mathbb P\in\bar{\mathcal P}}\Big\{\mathbb E_{X\sim\mathbb P}[f(X)]-\lambda\,\mathcal K_c(\widehat{\mathbb P},\mathbb P)\Big\}=\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}\big[f(X)-\lambda c(\widehat X,X)\big],$$
--   with the convention $0\cdot\infty=\infty$ in $\lambda c$.
--
--   This is the second chain of equalities in the proof of Theorem 1 (p. 4), obtained by unfolding the Kantorovich cost $\mathcal K_c(\widehat{\mathbb P},\mathbb P)=\inf_{\gamma\in\Gamma(\widehat{\mathbb P},\mathbb P)}\mathbb E_\gamma[c]$ in the soft-penalty value (P-soft). Combined with $(-\mathcal L)^*(-\lambda)=\text{(P-soft)}$ it yields the coupling representation of the conjugate used in both displays of Theorem 1. The case $\lambda=0$ is included because the second display of Theorem 1 minimizes over $\lambda\ge0$.
--
--   **Formalization note.** Expectations are `extIntegral` ($\int\varphi^+-\int\varphi^-$ with $\infty-\infty=-\infty$), the cost $\lambda\,\mathcal K_c$ on $\bar{\mathcal P}$ is the real product, and $\lambda c$ inside the coupling expectation is `lamMul` ($+\infty$ where $c=\infty$, also for $\lambda=0$).
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Theorem 1, p. 4, second display chain ("Using the definition of the Kantorovich transport cost (1), it follows that ...")

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality

theorem softValue_eq_couplingSup {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    softValue c f Phat lam = ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam) := by sorry

end ShortWDRODual.Legendre
