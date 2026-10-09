-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_theorem_1_D
-- name    : ShortWDRODual.Legendre.theorem_1_D
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:36.964815+00:00
-- url     : https://prove2.me/theorems/e7d09761-aba0-4f92-a747-c1942877eef9
-- title:
--   Theorem 1, (D), p. 3 — 𝓛(ρ) = min over λ ≥ 0 of λρ + 𝔼_ℙ̂[sup_x f(x) − λc(X̂, x)] for all ρ > 0 iff φ_λ satisfies (IP) for every λ > 0
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space, $f:\mathcal X\to\mathbb R$ a measurable function with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$, and $c:\mathcal X\times\mathcal X\to[0,\infty]$ a measurable transport cost with $c(x,x)=0$ for all $x$ (Assumption 1). For $\rho\ge0$ let
--   $$\mathcal L(\rho)=\sup_{\mathbb P\in\mathcal P(\mathcal X)}\big\{\mathbb E_{X\sim\mathbb P}[f(X)]:\mathcal K_c(\widehat{\mathbb P},\mathbb P)\le\rho\big\}$$
--   be the worst-case loss over the Kantorovich ball, and for $\lambda\ge0$ let $\phi_\lambda(\widehat x,x)=f(x)-\lambda c(\widehat x,x)$, with $0\cdot\infty=\infty$.
--
--   Then $\phi_\lambda$ satisfies the interchangeability principle (IP) for every $\lambda>0$ if and only if, for every $\lambda>0$, the function $\widehat x\mapsto\sup_x\phi_\lambda(\widehat x,x)$ is $\widehat{\mathbb P}$-measurable and
--   $$\mathcal L(\rho)=\min_{\lambda\ge0}\Big\{\lambda\rho+\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x\in\mathcal X}\{f(x)-\lambda c(\widehat X,x)\}\Big]\Big\}\qquad\forall\rho>0.\tag{D}$$
--
--   The duality formula (D) for Wasserstein distributionally robust optimization thus holds, with the minimum attained, exactly when the interchangeability principle holds for the penalized integrands; no topology on $\mathcal X$ and no regularity of $f$ or $c$ is assumed.
--
--   **Formalization Note** "min" is `IsLeast` (attained and a lower bound). Values are in `EReal`. Expectations use the published `extIntegral` ($\int\varphi^+-\int\varphi^-$, with $\infty-\infty=-\infty$, so laws with an undefined expectation never raise the supremum defining $\mathcal L$). The constraint $\mathcal K_c\le\rho$ is compared in `EReal`. The product $\lambda c$ follows the paper's $0\cdot\infty=\infty$. **Disclosed reading:** (IP) consists of the $\widehat{\mathbb P}$-measurability of the supremum function and an equality; (D) writes $\mathbb E_{\widehat{\mathbb P}}[\sup_x\cdots]$, which by §2.1 is an expectation of a measurable function. The right-hand side therefore carries the measurability of the supremum functions for $\lambda>0$ explicitly; without it the "if" direction would have to produce measurability from an equation, which the paper does not claim.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Theorem 1, (D), p. 3 (PDF p. 3); proof pp. 4–5 (PDF pp. 4–5)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality

theorem theorem_1_D {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0) :
    (∀ lam : ℝ, 0 < lam → IP Phat (phiLam c f lam)) ↔
      ((∀ lam : ℝ, 0 < lam → NullMeasurable (supFn (phiLam c f lam)) Phat) ∧
        ∀ ρ : ℝ, 0 < ρ →
          IsLeast {y : EReal | ∃ lam : ℝ, 0 ≤ lam ∧ y = ((lam * ρ : ℝ) : EReal) + dualG c f Phat lam}
            (robustLoss c f Phat ρ)) := by sorry

end ShortWDRODual.Legendre
