-- Prove2me | Theorems.Thm_ShortWDRODual_Tight_exists_eps_optimal_coupling
-- name    : ShortWDRODual.Tight.exists_eps_optimal_coupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:09.895511+00:00
-- url     : https://prove2.me/theorems/b365e55b-edca-4e13-9f17-f97346e5b868
-- title:
--   Proof of Proposition 2, pp. ec4–ec5 — if 𝔼_ℙ̂[Φ] < ∞, a Borel map T gives 𝔼_{(Id⊗T)#ℙ̂}[φ] > −6ε + 𝔼_ℙ̂[Φ]
-- statement:
--   Let $(\mathcal X,d)$ be a metric space with its Borel $\sigma$-algebra, $\widehat{\mathbb P}$ a tight probability measure, $f:\mathcal X\to\mathbb R$ a $\widehat{\mathbb P}$-measurable function with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$, $p\ge1$, $\lambda\ge0$, and put $\varphi(\widehat x,x)=f(x)-\lambda d(\widehat x,x)^p$, $\Phi(\widehat x)=\sup_x\varphi(\widehat x,x)$. Assume $\mathbb E_{\widehat{\mathbb P}}[\Phi]<+\infty$ and let $\epsilon>0$. Then there is a Borel measurable map $T:\mathcal X\to\mathcal X$ such that the coupling $\gamma=(\mathrm{Id}\otimes T)_\#\widehat{\mathbb P}$, the law of $(\widehat X,T(\widehat X))$ for $\widehat X\sim\widehat{\mathbb P}$, satisfies
--   $$\mathbb E_\gamma[\varphi]>-6\epsilon+\mathbb E_{\widehat{\mathbb P}}[\Phi].$$
--
--   Together with the easy inequality $\mathbb E_\gamma[\varphi]\le\mathbb E_{\widehat{\mathbb P}}[\Phi]$ this gives the interchangeability principle in the case $\mathbb E_{\widehat{\mathbb P}}[\Phi]<+\infty$, with near-optimal couplings that are deterministic.
--
--   **Formalization Note** Expectations are `extIntegral` (lower Lebesgue integrals, $\infty-\infty=-\infty$). The coupling is `Phat.map (fun x => (x, T x))`; it automatically has first marginal $\widehat{\mathbb P}$. The constant $6\epsilon$ is the paper's.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Proposition 2, pp. ec4–ec5 (PDF pp. 18–19), construction of T and the final display

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Tight_Setting

namespace ShortWDRODual.Tight

open MeasureTheory ModelRiskOT.Duality

/-- Proof of Proposition 2, arXiv:2205.00362v4, pp. ec4–ec5, case `𝔼_ℙ̂[Φ] < +∞`: for every
`ε > 0` there is a Borel-measurable selection map `T : 𝒳 → 𝒳` such that the coupling
`γ = (Id ⊗ T)_#ℙ̂` satisfies `𝔼_γ[φ] > −6ε + 𝔼_ℙ̂[Φ]`. -/
theorem exists_eps_optimal_coupling {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (htight : IsTightMeasureSet ({Phat} : Set (Measure X)))
    (f : X → ℝ) (hf : NullMeasurable f Phat)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (p : ℝ) (hp : 1 ≤ p) (lam : ℝ) (hlam : 0 ≤ lam)
    (hfin : extIntegral Phat (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : X → X, Measurable T ∧
      ((-6 * ε : ℝ) : EReal) + extIntegral Phat (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) <
        extIntegral (Phat.map (fun x => (x, T x))) (pWassIntegrand f lam p) := by sorry

end ShortWDRODual.Tight
