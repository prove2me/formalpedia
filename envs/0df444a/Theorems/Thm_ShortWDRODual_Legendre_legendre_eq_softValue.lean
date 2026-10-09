-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_legendre_eq_softValue
-- name    : ShortWDRODual.Legendre.legendre_eq_softValue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:21.795847+00:00
-- url     : https://prove2.me/theorems/9acd4e0d-dfc5-4c83-88ab-287b2bb8942b
-- title:
--   Proof of Theorem 1, p. 4 — for λ > 0, (−𝓛)*(−λ) equals the value of (P-soft)
-- statement:
--   Assume Assumption 1: $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ is a probability space, $f$ is measurable with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$, and $c:\mathcal X\times\mathcal X\to[0,\infty]$ is measurable with $c(x,x)=0$. Let $\mathcal L$ be the worst-case loss (P), with $\mathcal L(\rho)=-\infty$ for $\rho<0$, and let $(-\mathcal L)^*$ be the Legendre transform of $-\mathcal L$. Then for every $\lambda>0$,
--   $$(-\mathcal L)^*(-\lambda)=\sup_{\mathbb P\in\bar{\mathcal P}}\big\{\mathbb E_{X\sim\mathbb P}[f(X)]-\lambda\,\mathcal K_c(\widehat{\mathbb P},\mathbb P)\big\},$$
--   where $\bar{\mathcal P}$ is the set of probability measures $\mathbb P$ with $\mathcal K_c(\widehat{\mathbb P},\mathbb P)<\infty$.
--
--   This identifies the Legendre transform of the worst-case loss with the soft-penalty problem (P-soft), the first step of the proof of Theorem 1.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Theorem 1, p. 4 (PDF p. 4), first display, "which gives (P-soft)"

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality

theorem legendre_eq_softValue {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    legendre (fun ρ => - robustLoss c f Phat ρ) (-lam) = softValue c f Phat lam := by sorry

end ShortWDRODual.Legendre
