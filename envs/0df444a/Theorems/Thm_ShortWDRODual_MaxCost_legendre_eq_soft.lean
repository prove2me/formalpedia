-- Prove2me | Theorems.Thm_ShortWDRODual_MaxCost_legendre_eq_soft
-- name    : ShortWDRODual.MaxCost.legendre_eq_soft
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:25:18.930876+00:00
-- url     : https://prove2.me/theorems/cc10abad-bd07-45b2-9ce7-4ff98c8898fc
-- title:
--   Proof of Theorem 2, pp. ec8–ec9 — (−𝓛̄)*(−λ) = sup over ℙ of 𝔼_ℙ[f(X)] − λ𝒦̄_c(ℙ̂, ℙ) for λ ≥ 0
-- statement:
--   Let $\mathcal X$ be a Polish space with its Borel $\sigma$-algebra, $\widehat{\mathbb P}$ a probability measure on $\mathcal X$, $f:\mathcal X\to\mathbb R$ measurable with $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$, and $c:\mathcal X\times\mathcal X\to[0,\infty)$ continuous with $c(x,x)=0$. Let $\overline{\mathcal K}_c$ be the maximum transport cost and $\overline{\mathcal L}(\rho)=\sup_{\mathbb P}\{\mathbb E_{\mathbb P}[f(X)]:\overline{\mathcal K}_c(\widehat{\mathbb P},\mathbb P)\le\rho\}$ the maximum transport cost robust loss ($=-\infty$ for $\rho<0$). Then for every $\lambda\ge0$ the Legendre transform of $-\overline{\mathcal L}$ at $-\lambda$ is the soft-constrained robust loss:
--   $$(-\overline{\mathcal L})^*(-\lambda)=\sup_{\rho\in\mathbb R}\big\{(-\lambda)\rho-(-\overline{\mathcal L}(\rho))\big\}=\sup_{\mathbb P\in\mathcal P(\mathcal X)}\Big\{\mathbb E_{X\sim\mathbb P}[f(X)]-\lambda\,\overline{\mathcal K}_c(\widehat{\mathbb P},\mathbb P)\Big\},$$
--   with the convention $0\cdot\infty=\infty$ in $\lambda\overline{\mathcal K}_c$.
--
--   This is the dual computation in the proof of Theorem 2, which identifies the left side of Theorem 2's second display with the soft-penalty problem for the maximum transport cost, as announced in §5.1.
--
--   **Formalization Note** The page writes $\mathcal W_\infty$ for $\overline{\mathcal K}_c$ in this display; the Lean statement uses $\overline{\mathcal K}_c$, which is what the definitions of §5.1 call for. The supremum ranges over all probability measures on $\mathcal X$ (the paper's $\mathcal P(\mathcal X)$ restricts to finite Kantorovich cost; measures with $\overline{\mathcal K}_c=\infty$ contribute $-\infty$ on both sides). $\lambda\overline{\mathcal K}_c$ is `lamMul` (so $\lambda\cdot\infty=\infty$ also for $\lambda=0$); expectations are `extIntegral`, and `EReal` arithmetic gives $a-\infty=-\infty$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Theorem 2, "Next, we compute the dual", pp. ec8–ec9 (PDF pp. 22–23); §5.1 soft counterpart, p. 9

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting

namespace ShortWDRODual.MaxCost

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

/-- Proof of Theorem 2 (pp. ec8–ec9), the dual computation:
`(−𝓛̄)*(−λ) = sup_{ℙ ∈ 𝒫(𝒳)} {𝔼_ℙ[f(X)] − λ 𝒦̄_c(ℙ̂, ℙ)}` for `λ ≥ 0`, with `0 · ∞ = ∞`. -/
theorem legendre_eq_soft {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (hf : Measurable f) (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y) (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ShortWDRODual.Legendre.legendre (fun ρ => - robustLossMax c f Phat ρ) (-lam) =
      ⨆ (P : Measure X) (_ : IsProbabilityMeasure P),
        extIntegral P (fun x => (f x : EReal)) - ShortWDRODual.Legendre.lamMul lam (maxCost c Phat P) := by sorry

end ShortWDRODual.MaxCost
