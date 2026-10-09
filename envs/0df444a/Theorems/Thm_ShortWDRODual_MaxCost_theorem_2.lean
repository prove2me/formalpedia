-- Prove2me | Theorems.Thm_ShortWDRODual_MaxCost_theorem_2
-- name    : ShortWDRODual.MaxCost.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:25:09.556082+00:00
-- url     : https://prove2.me/theorems/18ddb88e-a3cd-4c3f-87bd-2ea0d9ee4f31
-- title:
--   Theorem 2, p. 10 — on a Polish space with continuous c, 𝓛̄(ρ) = 𝔼_ℙ̂[sup{f(x) : c(X̂, x) ≤ ρ}] and its Legendre dual
-- statement:
--   Let $\mathcal X$ be a Polish space with its Borel $\sigma$-algebra $\mathcal F$, $\widehat{\mathbb P}$ a probability measure on $\mathcal X$, $f:\mathcal X\to\mathbb R$ measurable with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$ (Assumption 1), and $c:\mathcal X\times\mathcal X\to[0,\infty)$ a continuous transport cost with $c(x,x)=0$ for all $x$. Let
--   $$\overline{\mathcal K}_c(\widehat{\mathbb P},\mathbb P)=\inf_{\gamma\in\Gamma(\widehat{\mathbb P},\mathbb P)}\gamma\text{-}\operatorname*{ess\,sup}_{\widehat x,x}c(\widehat x,x),\qquad\overline{\mathcal L}(\rho)=\sup_{\mathbb P\in\mathcal P(\mathcal X)}\big\{\mathbb E_{X\sim\mathbb P}[f(X)]:\overline{\mathcal K}_c(\widehat{\mathbb P},\mathbb P)\le\rho\big\}$$
--   be the maximum transport cost and its robust loss. Then
--
--   1. for every $\rho\ge0$,
--   $$\overline{\mathcal L}(\rho)=\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_x\big\{f(x):c(\widehat X,x)\le\rho\big\}\Big];$$
--   2. for every $\lambda\in\mathbb R$, the Legendre transform $(-\overline{\mathcal L})^*(-\lambda)=\sup_{\rho\in\mathbb R}\{(-\lambda)\rho+\overline{\mathcal L}(\rho)\}$ satisfies
--   $$(-\overline{\mathcal L})^*(-\lambda)=\sup_{\rho\ge0}\Big\{\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_x\big\{f(x):c(\widehat X,x)\le\rho\big\}\Big]-\lambda\rho\Big\}.$$
--
--   For $c=d$ a metric, $\overline{\mathcal K}_d$ is the $\infty$-Wasserstein distance, and the theorem reduces $\infty$-Wasserstein DRO to a nominal expectation of a local supremum. Remark 5 of the paper shows that the identity fails without continuity of $c$, even for a metric cost.
--
--   **Formalization Note** Expectations are the published `extIntegral` ($\int\varphi^+-\int\varphi^-$ with lower Lebesgue integrals, in $[-\infty,\infty]$, with $\infty-\infty=-\infty$); the integrand $\widehat x\mapsto\sup\{f(x):c(\widehat x,x)\le\rho\}$ is in general only universally measurable, and for such integrands the lower integral is the completed integral. The inner supremum is in `EReal`. $\overline{\mathcal L}$'s ball constraint is compared in `EReal`, so $\overline{\mathcal L}(\rho)=-\infty$ for $\rho<0$; the Legendre transform ranges over all real $\rho$, and the second display is stated for all real $\lambda$ since the page gives no range. The page prints an unmatched bracket in the second display; the bracketing used is the only one that parses. The paper's $\mathcal P(\mathcal X)$ restricts to finite Kantorovich cost, which $\overline{\mathcal K}_c\le\rho$ already implies.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Theorem 2, p. 10 (PDF p. 10); definitions §5.1, p. 9

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting

namespace ShortWDRODual.MaxCost

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

/-- Theorem 2 (p. 10): on a Polish space `𝒳` with a continuous cost `c : 𝒳 × 𝒳 → [0, ∞)`
vanishing on the diagonal, and for `f` satisfying Assumption 1,
`𝓛̄(ρ) = 𝔼_ℙ̂[sup_x {f(x) : c(X̂, x) ≤ ρ}]` for every `ρ ≥ 0`, and
`(−𝓛̄)*(−λ) = sup_{ρ ≥ 0} {𝔼_ℙ̂[sup_x {f(x) : c(X̂, x) ≤ ρ}] − λρ}` for every `λ`. -/
theorem theorem_2 {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (hf : Measurable f) (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y) (hc0 : ∀ x, c x x = 0) :
    (∀ ρ : ℝ, 0 ≤ ρ → robustLossMax c f Phat ρ = extIntegral Phat (localSup c f ρ)) ∧
    (∀ lam : ℝ, ShortWDRODual.Legendre.legendre (fun ρ => - robustLossMax c f Phat ρ) (-lam) =
      ⨆ (ρ : ℝ) (_ : 0 ≤ ρ),
        extIntegral Phat (localSup c f ρ) - ((lam * ρ : ℝ) : EReal)) := by sorry

end ShortWDRODual.MaxCost
