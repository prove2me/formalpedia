-- Prove2me | Theorems.Thm_PathRecording_lemma_5_5
-- name    : PathRecording.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:09:35.7451+00:00
-- url     : https://prove2.me/theorems/9340b5fd-1643-4a22-b65c-eef1e6d32695
-- title:
--   Lemma 5.5 — $\mathrm{Im}(\Theta_t\Omega_{\mathcal A_t})=\mathrm{Im}(\Theta_t)=F^{-1}(\mathrm{Tab}_t)$ and $\Gamma_tF\Theta_t=W_t\Omega_{\mathcal A_t}$
-- statement:
--   Let $G$ be a compact group with Haar probability measure, $\rho:G\to U(N)$ a continuous unitary representation, and fix Schur–Weyl data for $\rho^{\otimes t}$. Then
--   $$\mathrm{Im}(F\cdot\Theta_t\cdot\Omega_{\mathcal A_t})=\mathrm{Im}(F\cdot\Theta_t)=\mathrm{Tab}_t,$$
--   that is, the images of $\Theta_t\Omega_{\mathcal A_t}$ and of $\Theta_t$ in $L^2(G)$ are both $F^{-1}(\mathrm{Tab}_t)$; and, as operators on $\mathrm{Path}_t$,
--   $$\Gamma_t\cdot F\cdot\Theta_t=W_t\,\Omega_{\mathcal A_t}.\qquad(5.14)$$
--
--   Identity (5.14) is the bridge between the uncompressed oracle, which produces matrix-element functions $\Theta_t|\vec x,\vec y\rangle$, and the path-recording oracle, which manipulates the paths $|\vec x,\vec y\rangle$ themselves.
--
--   Differences from the source:
--   - generalization: G a compact Lie group with its normalized Haar measure dg → G any compact topological group with a Borel σ-algebra and a left Haar probability measure μ; reason: the Lie structure is never used; a compact Lie group is such a group, and on it (second countable) every left Haar probability measure is the normalized, regular, bi-invariant Haar measure of Definition 3.1; on a general compact group Lean also admits left Haar measures that are not regular, which only enlarges the statement
--   - encoding: the generalized Schur transform Schur_t : V^{⊗t} → ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t} (Definition 3.22, Theorem 3.11) → an arbitrary SchurWeylData ρ t: a finite label type (Ĝ_t), irreducible, pairwise non-isomorphic continuous unitary matrix irreps on ℂ^{dG λ}, multiplicity dimensions dA λ > 0, and a unitary matrix schur with schur ρ^{⊗t}(g) schur† = ⨁_λ ρ_λ(g) ⊗ I; reason: the paper's Schur transform is any such family; stating the result for every choice covers the paper's choice, and the operators depend on it only through its blocks
--   - encoding: Path_t = V^{⊗t} ⊗ \overline{V}^{⊗t} and the double Schur transform Schur_t ⊗ \overline{Schur_t} → vectors indexed by pairs (x⃗, y⃗) of Fin t → Fin N, and the Kronecker product of schur with its entrywise conjugate (inverse Schur_t† ⊗ Schur_tᵀ); reason: a linear map on the conjugate space is the conjugate matrix in the conjugate basis; same instances
--   - encoding: the Peter–Weyl Fourier transform F on L²(G), Γ_t on all blocks λ ∈ Ĝ and the subspace F⁻¹(Tab_t) → Γ_t on Tab_t only, fourierTrunc (the coefficients ⟪F⁻¹|λ,X,Y⟩, f⟫ for λ ∈ Ĝ_t, i.e. F followed by the projection onto Tab_t) and matrixCoeffSpace (the span of F⁻¹|λ,X,Y⟩ = √d_λ⟨Y|ρ_λ(·)|X⟩, λ ∈ Ĝ_t); reason: F is unitary with F⁻¹|λ,X,Y⟩ given by Definition 3.7, and Γ_t vanishes off Tab_t, so Γ_t·F = Γ_t·fourierTrunc and F⁻¹(Tab_t) is that span; same instances
--   - encoding: Im(F·Θ_t·Ω_{𝒜_t}) = Im(F·Θ_t) = Tab_t → Im(Θ_t Ω_{𝒜_t}) = Im(Θ_t) = matrixCoeffSpace as subsets of L²(G); reason: F is unitary and F⁻¹(Tab_t) = matrixCoeffSpace, so applying F⁻¹ gives the same statement
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Lemma 5.5, Eq. (5.14), p.64

import Mathlib
import Definitions.Def_PathRecording_fourier
import Definitions.Def_PathRecording_reweight

set_option autoImplicit false

namespace PathRecording

open Matrix MeasureTheory

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Lemma 5.5, p.64: "`Im(F · Θ_t · Ω_{𝒜_t}) = Im(F · Θ_t) = Tab_t`. Moreover, as
operators defined on `Path_t`, `Γ_t · F · Θ_t = W_t Ω_{𝒜_t}`. (5.14)"

**Formalization Note.** `F` is unitary, so `Im(F · Θ_t · Ω) = Tab_t` is `Im(Θ_t Ω) = F⁻¹(Tab_t)`,
stated as equality of subsets of `L²(G)` with `F⁻¹(Tab_t) = matrixCoeffSpace μ S`; likewise for
`Im(F · Θ_t)`. `Γ_t · F` is `gammaF μ S`. -/
theorem lemma_5_5 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {N : ℕ} {ρ : UnitaryRep G N} {t : ℕ} (S : SchurWeylData ρ t) :
    Set.range (fun v => theta μ ρ t (S.omega *ᵥ v)) = (matrixCoeffSpace μ S : Set (Lp ℂ 2 μ)) ∧
    Set.range (theta μ ρ t) = (matrixCoeffSpace μ S : Set (Lp ℂ 2 μ)) ∧
    ∀ v : PathIdx N t → ℂ, gammaF μ S (theta μ ρ t v) = (S.reweight * S.omega) *ᵥ v := by sorry

end PathRecording
