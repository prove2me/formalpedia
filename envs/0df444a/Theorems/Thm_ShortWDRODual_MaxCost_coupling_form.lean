-- Prove2me | Theorems.Thm_ShortWDRODual_MaxCost_coupling_form
-- name    : ShortWDRODual.MaxCost.coupling_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:25:29.579399+00:00
-- url     : https://prove2.me/theorems/18a43bb6-978d-4efc-9cf2-7b8cd7c5eb4d
-- title:
--   Proof of Theorem 2, p. ec8 — sup over γ ∈ Γ_ℙ̂ with γ-ess sup c ≤ ρ of 𝔼_γ[f(X)] equals 𝔼_ℙ̂[sup{f(x) : c(X̂, x) ≤ ρ}]
-- statement:
--   Let $\mathcal X$ be a Polish space with its Borel $\sigma$-algebra, $\widehat{\mathbb P}$ a probability measure on $\mathcal X$, $f:\mathcal X\to\mathbb R$ measurable with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$, and $c:\mathcal X\times\mathcal X\to[0,\infty)$ continuous with $c(x,x)=0$. Let $\Gamma_{\widehat{\mathbb P}}$ be the probability measures on $\mathcal X\times\mathcal X$ with first marginal $\widehat{\mathbb P}$. Then for every $\rho\ge0$,
--   $$\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\Big\{\mathbb E_{(\widehat X,X)\sim\gamma}[f(X)]:\gamma\text{-}\operatorname*{ess\,sup}_{\widehat x,x\in\mathcal X}c(\widehat x,x)\le\rho\Big\}=\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_x\big\{f(x):c(\widehat X,x)\le\rho\big\}\Big].$$
--
--   This is the content of the last three lines of the first chain in the proof of Theorem 2: once the worst-case distribution is parametrized by a coupling, the worst case is attained by moving each nominal point to a best point of its $c$-ball.
--
--   **Formalization Note** Expectations are `extIntegral` (in $[-\infty,\infty]$, with $\infty-\infty=-\infty$). The essential supremum is Mathlib's `essSup` of $\mathrm{ofReal}\circ c$ under $\gamma$, compared with $\mathrm{ofReal}(\rho)$ in $[0,\infty]$. The inner supremum is taken in `EReal`, so it is $+\infty$ where $f$ is unbounded above on the ball; the integrand is in general only universally measurable, and `extIntegral` uses lower Lebesgue integrals, which agree with the completed integral for such integrands.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Theorem 2, p. ec8 (PDF p. 22), first display chain, lines 4–7

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting

namespace ShortWDRODual.MaxCost

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

/-- Proof of Theorem 2 (p. ec8), last three lines of the first chain:
`sup_{γ ∈ Γ_ℙ̂} {𝔼_γ[f(X)] : γ-ess sup c ≤ ρ} = 𝔼_ℙ̂[sup_x {f(x) : c(X̂, x) ≤ ρ}]`. -/
theorem coupling_form {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (hf : Measurable f) (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y) (hc0 : ∀ x, c x x = 0)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (⨆ γ ∈ {γ : Measure (X × X) | γ ∈ ShortWDRODual.Legendre.couplingsFst Phat ∧
        essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ ≤ ENNReal.ofReal ρ},
        extIntegral γ (fun q => (f q.2 : EReal))) =
      extIntegral Phat (localSup c f ρ) := by sorry

end ShortWDRODual.MaxCost
