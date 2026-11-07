-- Prove2me | Theorems.Thm_PathRecording_first_claim
-- name    : PathRecording.first_claim
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:09:27.875978+00:00
-- url     : https://prove2.me/theorems/124529f5-4f68-4910-bbfd-a0234dc99996
-- title:
--   p.67 — first claim of Theorem 5.3: $Q^{\mathrm{Path}}_{\rho,t+1}(I_V\otimes\Gamma_tF)=(I_V\otimes\Gamma_{t+1}F)Q_\rho$ on $V\otimes F^{-1}(\mathrm{Tab}_t)$
-- statement:
--   Let $G$ be a compact group with Haar probability measure, $\rho:G\to U(N)$ a continuous unitary representation, and fix Schur–Weyl data for every $\rho^{\otimes t}$. Let $\Gamma_t=(\mathrm{Schur}_t^\dagger\otimes\mathrm{Schur}_t^\top)E_t$. For every $t$ and every $\varphi\in V\otimes F^{-1}(\mathrm{Tab}_t)$,
--   $$Q^{\mathrm{Path}}_{\rho,t+1}\,(I_V\otimes\Gamma_tF)\,\varphi=(I_V\otimes\Gamma_{t+1}F)\,Q_\rho\,\varphi.\qquad(5.12)$$
--
--   One query to the path-recording oracle, applied to the image of an uncompressed state, gives the image of the uncompressed state after one query to $Q_\rho$.
--
--   Differences from the source:
--   - generalization: G a compact Lie group with its normalized Haar measure dg → G any compact topological group with a Borel σ-algebra and a left Haar probability measure μ; reason: the Lie structure is never used; a compact Lie group is such a group, and on it (second countable) every left Haar probability measure is the normalized, regular, bi-invariant Haar measure of Definition 3.1; on a general compact group Lean also admits left Haar measures that are not regular, which only enlarges the statement
--   - encoding: the generalized Schur transform Schur_t : V^{⊗t} → ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t} (Definition 3.22, Theorem 3.11) → an arbitrary SchurWeylData ρ t: a finite label type (Ĝ_t), irreducible, pairwise non-isomorphic continuous unitary matrix irreps on ℂ^{dG λ}, multiplicity dimensions dA λ > 0, and a unitary matrix schur with schur ρ^{⊗t}(g) schur† = ⨁_λ ρ_λ(g) ⊗ I; reason: the paper's Schur transform is any such family; stating the result for every choice covers the paper's choice, and the operators depend on it only through its blocks
--   - encoding: Path_t = V^{⊗t} ⊗ \overline{V}^{⊗t} and the double Schur transform Schur_t ⊗ \overline{Schur_t} → vectors indexed by pairs (x⃗, y⃗) of Fin t → Fin N, and the Kronecker product of schur with its entrywise conjugate (inverse Schur_t† ⊗ Schur_tᵀ); reason: a linear map on the conjugate space is the conjugate matrix in the conjugate basis; same instances
--   - encoding: the Peter–Weyl Fourier transform F on L²(G), Γ_t on all blocks λ ∈ Ĝ and the subspace F⁻¹(Tab_t) → Γ_t on Tab_t only, fourierTrunc (the coefficients ⟪F⁻¹|λ,X,Y⟩, f⟫ for λ ∈ Ĝ_t, i.e. F followed by the projection onto Tab_t) and matrixCoeffSpace (the span of F⁻¹|λ,X,Y⟩ = √d_λ⟨Y|ρ_λ(·)|X⟩, λ ∈ Ĝ_t); reason: F is unitary with F⁻¹|λ,X,Y⟩ given by Definition 3.7, and Γ_t vanishes off Tab_t, so Γ_t·F = Γ_t·fourierTrunc and F⁻¹(Tab_t) is that span; same instances
--   - encoding: V ⊗ L²(G) with Q_ρ(|x⟩⊗|f⟩) = ∫ f(g) ρ(g)|x⟩⊗|g⟩ dg → Fin N → Lp ℂ 2 μ, with (Q_ρ φ)_y = Σ_x ⟨y|ρ(·)|x⟩ · φ_x (multiplication by the continuous matrix entries as L^∞ functions); reason: (4.1) extended linearly; V ⊗ L²(G) ≅ L²(G)^N
--   - generalization: one Fourier transform F, with one fixed basis of each V_λ, on both sides of (5.12) → Γ_tF_t built from the irrep matrices of the data at t and Γ_{t+1}F_{t+1} from those of the data at t+1, which may use different bases or representatives; reason: the paper's fixed F is the case where the data at all t share their irrep matrices; the identity holds for every family
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, p.67 (first claim of Theorem 5.3, Eq. (5.12), p.63)

import Mathlib
import Definitions.Def_PathRecording_fourier
import Definitions.Def_PathRecording_pathOracle

set_option autoImplicit false

namespace PathRecording

open Matrix MeasureTheory

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, p.67 (first claim of Theorem 5.3, Eq. (5.12)): for the explicit partial
isometries `Γ_t = (Schur_t† ⊗ Schur_tᵀ) E_t` of §5.3 and every Schur–Weyl data family,
`Q^{Path}_{ρ,t+1} (I_V ⊗ Γ_t F) = (I_V ⊗ Γ_{t+1} F) Q_ρ` on inputs in `V ⊗ F⁻¹(Tab_t)`.

**Formalization Note.** A state of `V ⊗ L²(G)` is `φ : Fin N → L²(G)`; it lies in
`V ⊗ F⁻¹(Tab_t)` when every component lies in `matrixCoeffSpace μ (S t)`. `(I_V ⊗ Γ_t F) φ` is the
vector `(x, p) ↦ (Γ_t F φ_x)_p` of `V ⊗ Path_t`. -/
theorem first_claim {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {N : ℕ} {ρ : UnitaryRep G N} (S : (t : ℕ) → SchurWeylData ρ t) (t : ℕ)
    (φ : Fin N → Lp ℂ 2 μ) (hφ : ∀ x, φ x ∈ matrixCoeffSpace μ (S t)) :
    (fun q : Fin N × PathIdx N (t + 1) => gammaF μ (S (t + 1)) (oracle μ ρ φ q.1) q.2) =
      pathOracle (S t) (S (t + 1)) *ᵥ fun q : Fin N × PathIdx N t => gammaF μ (S t) (φ q.1) q.2 := by sorry

end PathRecording
