-- Prove2me | Theorems.Thm_ShortWDRODual_MaxCost_IP_psi
-- name    : ShortWDRODual.MaxCost.IP_psi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:27:23.955608+00:00
-- url     : https://prove2.me/theorems/1d134d85-47a0-4f9e-a9f3-f8552763fbd2
-- title:
--   Proof of Theorem 2, p. ec8 — ψ_ρ = f − ∞·1{c > ρ} satisfies (IP) on a Polish space for every ρ ≥ 0
-- statement:
--   Let $\mathcal X$ be a Polish space with its Borel $\sigma$-algebra, $\widehat{\mathbb P}$ a probability measure on $\mathcal X$, $f:\mathcal X\to\mathbb R$ a measurable function, and $c:\mathcal X\times\mathcal X\to[0,\infty)$ a continuous cost with $c(x,x)=0$ for all $x$. For $\rho\ge0$ define
--   $$\psi_\rho(\widehat x,x)=f(x)-\infty\,\mathbf 1\{c(\widehat x,x)>\rho\}=\begin{cases}f(x),&c(\widehat x,x)\le\rho,\\-\infty,&c(\widehat x,x)>\rho.\end{cases}$$
--   Then $\psi_\rho$ satisfies the interchangeability principle (IP): $\widehat x\mapsto\sup_x\psi_\rho(\widehat x,x)$ is $\widehat{\mathbb P}$-measurable and
--   $$\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x}\psi_\rho(\widehat X,x)\Big]=\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}\big[\psi_\rho(\widehat X,X)\big].$$
--
--   This is the step of the proof of Theorem 2 that exchanges the supremum over couplings with the expectation of a pointwise supremum; the paper invokes it as "(IP) as it holds for all measurable functions according to Example 2". The function $\psi_\rho$ is Borel and diagonally dominant, since $c(x,x)=0\le\rho$.
--
--   **Formalization Note** In $\psi_\rho$ the product $\infty\cdot\mathbf 1\{\cdot\}$ is read with $\infty\cdot 0=0$, as the next line of the paper's proof requires (with the paper's global convention $0\cdot\infty=\infty$, $\psi_\rho$ would be identically $-\infty$). Expectations are `extIntegral` (with $\infty-\infty=-\infty$); $\widehat{\mathbb P}$-measurability is `NullMeasurable`. The loss condition $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$ is not needed for this step and is not assumed.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Theorem 2, p. ec8 (PDF p. 22), "Here we used (IP) as it holds for all measurable functions according to Example 2"

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting

namespace ShortWDRODual.MaxCost

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

/-- Proof of Theorem 2 (p. ec8): on a Polish space with a continuous cost
`c : 𝒳 × 𝒳 → [0, ∞)` vanishing on the diagonal, and for a measurable `f : 𝒳 → ℝ`, the function
`ψ_ρ(x̂, x) = f(x) − ∞·1{c(x̂, x) > ρ}` satisfies (IP) for every `ρ ≥ 0`. -/
theorem IP_psi {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (hf : Measurable f)
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y) (hc0 : ∀ x, c x x = 0)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ShortWDRODual.Legendre.IP Phat (psi c f ρ) := by sorry

end ShortWDRODual.MaxCost
