-- Prove2me | Theorems.Thm_ShortWDRODual_Tight_integral_le_supFn
-- name    : ShortWDRODual.Tight.integral_le_supFn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:17.574575+00:00
-- url     : https://prove2.me/theorems/ecdf3a95-bed6-4155-9d5e-c2fb0d41bad8
-- title:
--   Proof of Proposition 2, p. ec4 — 𝔼_γ[φ] ≤ 𝔼_ℙ̂[Φ] for every γ ∈ Γ_ℙ̂
-- statement:
--   Let $(\mathcal X,d)$ be a metric space with its Borel $\sigma$-algebra $\mathcal F$, $\widehat{\mathbb P}$ a tight probability measure on it, $f:\mathcal X\to\mathbb R$ a $\widehat{\mathbb P}$-measurable function with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$, $p\ge1$ and $\lambda\ge0$. With $\varphi(\widehat x,x)=f(x)-\lambda d(\widehat x,x)^p$ and $\Phi(\widehat x)=\sup_x\varphi(\widehat x,x)$, every probability measure $\gamma$ on $\mathcal X\times\mathcal X$ with first marginal $\widehat{\mathbb P}$ satisfies
--   $$\mathbb E_{(\widehat X,X)\sim\gamma}[\varphi(\widehat X,X)]\le\mathbb E_{\widehat X\sim\widehat{\mathbb P}}[\Phi(\widehat X)].$$
--
--   This is the easy half of the interchangeability principle for the $p$-Wasserstein integrand.
--
--   **Formalization Note** Expectations are `extIntegral`, i.e. $\int\varphi^+-\int\varphi^-$ in the extended reals with lower Lebesgue integrals and $\infty-\infty=-\infty$; for $\varphi$, which need not be $\mathcal F\otimes\mathcal F$-measurable, this is the reading of $\mathbb E_\gamma[\varphi]$ fixed in the setting module. Tightness of $\widehat{\mathbb P}$ is kept as on the page, although this step may not need it.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Proposition 2, p. ec4 (PDF p. 18), second sentence

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Tight_Setting

namespace ShortWDRODual.Tight

open MeasureTheory ModelRiskOT.Duality

/-- Proof of Proposition 2, arXiv:2205.00362v4, p. ec4: for any `γ ∈ Γ_ℙ̂`,
`𝔼_γ[φ] ≤ 𝔼_ℙ̂[Φ]`, where `φ(x̂, x) = f(x) − λ d(x̂, x)^p` and `Φ(x̂) = sup_x φ(x̂, x)`. -/
theorem integral_le_supFn {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (htight : IsTightMeasureSet ({Phat} : Set (Measure X)))
    (f : X → ℝ) (hf : NullMeasurable f Phat)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (p : ℝ) (hp : 1 ≤ p) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ γ ∈ ShortWDRODual.Legendre.couplingsFst Phat,
      extIntegral γ (pWassIntegrand f lam p) ≤ extIntegral Phat (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) := by sorry

end ShortWDRODual.Tight
