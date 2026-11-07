-- Prove2me | Theorems.Thm_PathRecording_claim_5_4
-- name    : PathRecording.claim_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:09:21.649562+00:00
-- url     : https://prove2.me/theorems/e5d844c6-8d72-4f05-a1b8-d26405926d58
-- title:
--   Claim 5.4 — $\Gamma_t$ is an isometry onto $\mathrm{Im}(\Omega_{\mathcal A_t})$, and so is $\Gamma_tF$ on $F^{-1}(\mathrm{Tab}_t)$
-- statement:
--   Let $G$ be a compact group with Haar probability measure, $\rho:G\to U(N)$ a continuous unitary representation, and fix Schur–Weyl data for $\rho^{\otimes t}$. Then:
--
--   1. $\Gamma_t^\dagger\Gamma_t=\Pi_{\mathrm{Tab}_t}$ and $\Gamma_t\Gamma_t^\dagger=\Omega_{\mathcal A_t}$, so $\Gamma_t$ is an isometry from $\mathrm{Tab}_t$ onto the legal path subspace $\mathrm{Im}(\Omega_{\mathcal A_t})\subset\mathrm{Path}_t$;
--   2. $\Gamma_tF$ preserves inner products on $F^{-1}(\mathrm{Tab}_t)$: $\langle\Gamma_tFf\,|\,\Gamma_tFf'\rangle=\langle f|f'\rangle$ for $f,f'\in F^{-1}(\mathrm{Tab}_t)$;
--   3. $\Gamma_tF$ maps $F^{-1}(\mathrm{Tab}_t)$ onto $\mathrm{Im}(\Omega_{\mathcal A_t})$.
--
--   This is the isometry through which the path-recording register represents the uncompressed recording register.
--
--   Differences from the source:
--   - generalization: G a compact Lie group with its normalized Haar measure dg → G any compact topological group with a Borel σ-algebra and a left Haar probability measure μ; reason: the Lie structure is never used; a compact Lie group is such a group, and on it (second countable) every left Haar probability measure is the normalized, regular, bi-invariant Haar measure of Definition 3.1; on a general compact group Lean also admits left Haar measures that are not regular, which only enlarges the statement
--   - encoding: the generalized Schur transform Schur_t : V^{⊗t} → ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t} (Definition 3.22, Theorem 3.11) → an arbitrary SchurWeylData ρ t: a finite label type (Ĝ_t), irreducible, pairwise non-isomorphic continuous unitary matrix irreps on ℂ^{dG λ}, multiplicity dimensions dA λ > 0, and a unitary matrix schur with schur ρ^{⊗t}(g) schur† = ⨁_λ ρ_λ(g) ⊗ I; reason: the paper's Schur transform is any such family; stating the result for every choice covers the paper's choice, and the operators depend on it only through its blocks
--   - encoding: Path_t = V^{⊗t} ⊗ \overline{V}^{⊗t} and the double Schur transform Schur_t ⊗ \overline{Schur_t} → vectors indexed by pairs (x⃗, y⃗) of Fin t → Fin N, and the Kronecker product of schur with its entrywise conjugate (inverse Schur_t† ⊗ Schur_tᵀ); reason: a linear map on the conjugate space is the conjugate matrix in the conjugate basis; same instances
--   - encoding: the Peter–Weyl Fourier transform F on L²(G), Γ_t on all blocks λ ∈ Ĝ and the subspace F⁻¹(Tab_t) → Γ_t on Tab_t only, fourierTrunc (the coefficients ⟪F⁻¹|λ,X,Y⟩, f⟫ for λ ∈ Ĝ_t, i.e. F followed by the projection onto Tab_t) and matrixCoeffSpace (the span of F⁻¹|λ,X,Y⟩ = √d_λ⟨Y|ρ_λ(·)|X⟩, λ ∈ Ĝ_t); reason: F is unitary with F⁻¹|λ,X,Y⟩ given by Definition 3.7, and Γ_t vanishes off Tab_t, so Γ_t·F = Γ_t·fourierTrunc and F⁻¹(Tab_t) is that span; same instances
--   - encoding: "Γ_t is an isometry between Tab_t and Im(Ω_{𝒜_t})" → Γ_t†Γ_t = I_{Tab_t} and Γ_tΓ_t† = Ω_{𝒜_t}; reason: these are the identities the page proves the claim with; together they say exactly that Γ_t is an isometry of Tab_t onto Im Ω_{𝒜_t}
--   - encoding: "Γ_t·F is an isometry between F⁻¹(Tab_t) and Im(Ω_{𝒜_t})" → Γ_tF preserves inner products on matrixCoeffSpace and its image of matrixCoeffSpace is the range of Ω_{𝒜_t}; reason: an isometry between two spaces is an inner-product-preserving map onto the second
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Claim 5.4, p.64 (with the computation of Γ_t†Γ_t and Γ_tΓ_t† above it)

import Mathlib
import Definitions.Def_PathRecording_fourier

set_option autoImplicit false

namespace PathRecording

open Matrix MeasureTheory
open scoped InnerProductSpace

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Claim 5.4, p.64: "`Γ_t` is an isometry between `Tab_t` and the legal path
subspace `Im(Ω_{𝒜_t}) ⊂ Path_t`. As a result, we see that `Γ_t · F` is an isometry between
`F⁻¹(Tab_t)` and `Im(Ω_{𝒜_t})`." Stated as:
1. `Γ_t† Γ_t = I_{Tab_t}` and `Γ_t Γ_t† = Ω_{𝒜_t}` (computed on p.64);
2. `Γ_t F` preserves inner products on `F⁻¹(Tab_t)`;
3. `Γ_t F` maps `F⁻¹(Tab_t)` onto `Im(Ω_{𝒜_t})`.

**Formalization Note.** `F⁻¹(Tab_t)` is `matrixCoeffSpace μ S` and `Γ_t F` is `gammaF μ S`
(see the `fourier` definitions). Inner products on `Path_t` are `Σ_p \overline{u_p} v_p`. -/
theorem claim_5_4 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {N : ℕ} {ρ : UnitaryRep G N} {t : ℕ} (S : SchurWeylData ρ t) :
    S.Gammaᴴ * S.Gamma = 1 ∧
    S.Gamma * S.Gammaᴴ = S.omega ∧
    (∀ f ∈ matrixCoeffSpace μ S, ∀ f' ∈ matrixCoeffSpace μ S,
      star (gammaF μ S f) ⬝ᵥ gammaF μ S f' = ⟪f, f'⟫_ℂ) ∧
    gammaF μ S '' (matrixCoeffSpace μ S : Set (Lp ℂ 2 μ)) = Set.range (S.omega *ᵥ ·) := by sorry

end PathRecording
