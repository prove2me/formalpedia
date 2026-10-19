-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_lemma_A_1
-- name    : SimpleCorrMFG.Conv.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:48.211643+00:00
-- url     : https://prove2.me/theorems/e0aa63c1-f371-4013-b200-dc8b6d30c6b8
-- title:
--   Lemma A.1, p. 27 — an almost-everywhere continuous relation $Y_n=\Psi(Z_n)$ passes to the limit in distribution
-- statement:
--   Let $\mathcal Y,\mathcal Z$ be Polish spaces. For $n\in\mathbb N$ let $Y_n,Z_n$ be random variables on probability spaces $(\Omega_n,\mathcal F_n,P_n)$ with values in $\mathcal Y$ and $\mathcal Z$, and let $(Y,Z)$ be a $\mathcal Y\times\mathcal Z$-valued random variable on $(\Omega,\mathcal F,P)$. Let $\Psi:\mathcal Z\to\mathcal Y$ be measurable. Suppose that $(Y_n,Z_n)\to(Y,Z)$ in distribution, that $Y_n=\Psi(Z_n)$ $P_n$-almost surely for every $n$, and that $\Psi$ is continuous at $P\circ Z^{-1}$-almost every point. Then
--   $$Y=\Psi(Z)\qquad P\text{-almost surely}.$$
--
--   The lemma transfers the dynamics of the $N$-player systems to their limit points; the mapping theorem alone would require $\Psi$ to be continuous everywhere, which fails for the system functions of interest (Remark 6.2).
--
--   **Formalization Note** The probability spaces may vary with $n$; convergence in distribution is Mathlib's `TendstoInDistribution` (weak convergence of the laws).
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, p. 27, Lemma A.1 (with the standing assumptions of Appendix A, p. 27)

import Mathlib

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Lemma A.1 (p. 27). -/
theorem lemma_A_1 {𝒴 𝒵 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    [TopologicalSpace 𝒵] [PolishSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (Yn : ∀ n, Ω n → 𝒴) (Zn : ∀ n, Ω n → 𝒵) (hYn : ∀ n, Measurable (Yn n))
    (hZn : ∀ n, Measurable (Zn n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → 𝒴) (Z : Ω' → 𝒵) (hY : Measurable Y) (hZ : Measurable Z)
    (Ψ : 𝒵 → 𝒴) (hΨ : Measurable Ψ)
    (hconv : TendstoInDistribution (fun n ω => (Yn n ω, Zn n ω)) atTop (fun ω => (Y ω, Z ω)) P P')
    (hYΨ : ∀ n, Yn n =ᵐ[P n] (Ψ ∘ Zn n))
    (hcont : ∀ᵐ z ∂(P'.map Z), ContinuousAt Ψ z) :
    Y =ᵐ[P'] (Ψ ∘ Z) := by sorry

end SimpleCorrMFG.Conv
