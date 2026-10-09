-- Prove2me | Theorems.Thm_RFRidge_Basic_lemma_1
-- name    : RFRidge.Basic.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:37.878017+00:00
-- url     : https://prove2.me/theorems/e95aa69d-e626-4d8f-853b-559ca9b487da
-- title:
--   Lemma 1, p. 19 — the integral operator of K is L = ∫ ψ_ω ⊗ ψ_ω dπ(ω), in the form ⟨f, Lg⟩ = ∫⟨f, ψ_ω⟩⟨g, ψ_ω⟩ dπ(ω)
-- statement:
--   Let $K$ be the kernel (6) of random features $\psi$ with feature law $\pi$, satisfying Assumption 3 ($\psi$ continuous, jointly measurable, $|\psi|\le\kappa$, $\kappa\ge1$). Let $\rho_X$ be a probability measure on $X$, let $L$ be the integral operator $(Lg)(x)=\int_X K(x,z)g(z)\,d\rho_X(z)$ on $L^2(X,\rho_X)$, and write $\psi_\omega=\psi(\cdot,\omega)$. Then $L=\int\psi_\omega\otimes\psi_\omega\,d\pi(\omega)$, that is, for all $f,g\in L^2(X,\rho_X)$,
--   $$\int_X f(x)\Big(\int_X K(x,z)g(z)\,d\rho_X(z)\Big)d\rho_X(x)=\int_\Omega\langle f,\psi_\omega\rangle_{\rho_X}\,\langle g,\psi_\omega\rangle_{\rho_X}\,d\pi(\omega).$$
--
--   The representation of $L$ as an average of rank-one operators is what links the kernel to its random-feature approximation; it is used in Lemma 2.
--
--   **Formalization Note** Equality of the bounded operators $L$ and $\int\psi_\omega\otimes\psi_\omega\,d\pi$ is equality of all their bilinear forms $\langle f,\cdot\,g\rangle_{\rho_X}$; this is the form the proof establishes and the form Lemma 2 uses. $f,g$ are functions in $L^2$ (`MemLp f 2`), and the inner products are written as integrals.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Lemma 1, p. 19 (proof p. 20)

import Mathlib
import Definitions.Def_RFRidge_Basic_Model

namespace RFRidge.Basic

open MeasureTheory

/-- Lemma 1, p. 19, in the bilinear-form version its proof establishes: under Assumption 3, for all
`f, g ∈ L²(X, ρ_X)`, `⟨f, L g⟩_{ρ_X} = ∫ ⟨f, ψ_ω⟩_{ρ_X} ⟨g, ψ_ω⟩_{ρ_X} dπ(ω)`, where
`(L g)(x) = ∫ K(x, z) g(z) dρ_X(z)` is the integral operator of the kernel (6). -/
theorem lemma_1 {X W : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
    (π : Measure W) [IsProbabilityMeasure π] (ψ : X → W → ℝ) (κ : ℝ) (hA : RFAssumptions ψ κ)
    (ρX : Measure X) [IsProbabilityMeasure ρX]
    (f g : X → ℝ) (hf : MemLp f 2 ρX) (hg : MemLp g 2 ρX) :
    ∫ x, f x * (∫ z, kernelOf π ψ x z * g z ∂ρX) ∂ρX
      = ∫ ω, (∫ x, f x * ψ x ω ∂ρX) * (∫ z, g z * ψ z ω ∂ρX) ∂π := by sorry

end RFRidge.Basic
