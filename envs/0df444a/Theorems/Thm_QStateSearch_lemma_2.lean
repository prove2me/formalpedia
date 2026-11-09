-- Prove2me | Theorems.Thm_QStateSearch_lemma_2
-- name    : QStateSearch.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:16:10.507284+00:00
-- url     : https://prove2.me/theorems/7e72183d-e00f-484f-b863-1b943957298c
-- title:
--   Lemma 2 — $\mathbb E_{\Psi\leftarrow\nu}\langle\Psi|\rho|\Psi\rangle\le(1+\ln(1/p))/D$ for $p$-uniform $\nu$
-- statement:
--   Let $D\ge2$, let $\mu_D$ be the Haar (uniform) probability measure on unit vectors of $\mathbb C^D$, let $0<p\le1$, and let $\nu$ be a $p$-uniform probability measure, $p\,\nu\le\mu_D$. Let $\rho$ be a density operator on $\mathbb C^D$. Then $\Psi\mapsto\langle\Psi|\rho|\Psi\rangle$ is $\nu$-integrable and
--   $$
--   \mathbb E_{\Psi\leftarrow\nu}\big[\langle\Psi|\rho|\Psi\rangle\big]\le\frac{1+\ln(1/p)}{D}.
--   $$
--
--   Conditioning a Haar-random state on an event of probability $p$ raises its expected overlap with any fixed state from $1/D$ to at most $(1+\ln(1/p))/D$. This is the geometric lemma of Aaronson and Kuperberg (Lemma 3.2 there), which the paper cites without proof; in Lemma 3 it is applied with $p=\mu_D(C(h))$.
--
--   **Formalization Note** $\nu$ is a measure on $\mathbb C^D$ with $p\nu\le\mu_D$; such a $\nu$ is supported on the unit sphere.
--
--   Differences from the source:
--   - generalization: $\nu$ a $p$-uniform probability measure on $\mathbb{CP}^{D-1}$ → $\nu$ a probability measure on $\mathbb C^D$ with $p\nu\le\mu_D$ for the uniform measure on the unit sphere; reason: a $p$-uniform measure on $\mathbb{CP}^{D-1}$ lifts (averaging over the phase) to such a measure on the sphere with the same expectation of the phase-invariant integrand
--   - generalization: the bound on $\mathbb E_\nu\langle\Psi|\rho|\Psi\rangle$ → integrability of the integrand and the bound; reason: the integrand is bounded and measurable on the support of the measure; stating integrability excludes a Bochner integral that is $0$ by convention
--   - encoding: $\langle\Psi|\rho|\Psi\rangle$, $\ln$ → the real part of $\overline{\psi}^{\mathsf T}\rho\psi$, `Real.log`; reason: $\langle\psi|\rho|\psi\rangle$ is real for Hermitian $\rho$
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Lemma 2, p.10

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_uniformSphere
import Definitions.Def_QStateSearch_IsPUniform
import Definitions.Def_WildeQIT_IsDensityOperator
open Matrix MeasureTheory OptimalSpectrum.Entangled

namespace QStateSearch

/-- **Lemma 2** (Haar overlap under conditioning; Aaronson–Kuperberg, Lemma 3.2). If `ν` is
`p`-uniform with respect to the Haar measure `μ_D` and `ρ` is a density operator on `ℂ^D`,
`D ≥ 2`, then `E_{Ψ←ν}[⟨Ψ|ρ|Ψ⟩] ≤ (1 + ln(1/p))/D`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Lemma 2, p.10.

**Formalization Note.** `ν` is a measure on `ℂ^D` with `p ν ≤ μ_D`, where `μ_D` is the uniform
probability measure on the unit sphere (`uniformSphere D`); a measure on `CP^{D−1}` lifts to
one on the sphere, and conversely, so this covers the paper's statement. `⟨ψ|ρ|ψ⟩` is
`re (star ψ ⬝ᵥ ρ *ᵥ ψ)`; `ln` is `Real.log`. The integrability conjunct rules out a junk Bochner
integral. -/
theorem lemma_2 (D : ℕ) (hD : 2 ≤ D) (p : ℝ) (ν : Measure (EuclideanSpace ℂ (Fin D)))
    (hν : IsPUniform (uniformSphere D) ν p) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) :
    Integrable (fun ψ : EuclideanSpace ℂ (Fin D) => (star (⇑ψ) ⬝ᵥ (ρ *ᵥ ⇑ψ)).re) ν ∧
      ∫ ψ, (star (⇑ψ) ⬝ᵥ (ρ *ᵥ ⇑ψ)).re ∂ν ≤ (1 + Real.log (1 / p)) / D := by sorry

end QStateSearch
