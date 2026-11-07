-- Prove2me | Theorems.Thm_PathRecording_lemma_5_7
-- name    : PathRecording.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:10:32.314848+00:00
-- url     : https://prove2.me/theorems/ab46365f-5b02-4819-be8b-48f9ddeb2011
-- title:
--   Lemma 5.7 — reachable recording states lie in $\mathrm{Im}(\Theta_t)=F^{-1}(\mathrm{Tab}_t)$
-- statement:
--   Let $G$ be a compact group with Haar probability measure and $\rho:G\to U(N)$ a continuous unitary representation. Fix any adaptive quantum algorithm whose query register is $V$ and which queries $Q_\rho$: a finite workspace $B$, unitaries $A_1,A_2,\dots$ on $V\otimes B$ applied between queries, and a start state $\psi$. Then after every number $i$ of queries, each component of the recording register (for each basis state of $V\otimes B$) lies in
--   $$\mathrm{Im}(\Theta_i)=F^{-1}(\mathrm{Tab}_i),$$
--   the latter for every choice of Schur–Weyl data at $i$.
--
--   This is why the restriction of (5.12) to $V\otimes F^{-1}(\mathrm{Tab}_t)$ costs nothing for query algorithms.
--
--   Differences from the source:
--   - generalization: G a compact Lie group with its normalized Haar measure dg → G any compact topological group with a Borel σ-algebra and a left Haar probability measure μ; reason: the Lie structure is never used; a compact Lie group is such a group, and on it (second countable) every left Haar probability measure is the normalized, regular, bi-invariant Haar measure of Definition 3.1; on a general compact group Lean also admits left Haar measures that are not regular, which only enlarges the statement
--   - encoding: the generalized Schur transform Schur_t : V^{⊗t} → ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t} (Definition 3.22, Theorem 3.11) → an arbitrary SchurWeylData ρ t: a finite label type (Ĝ_t), irreducible, pairwise non-isomorphic continuous unitary matrix irreps on ℂ^{dG λ}, multiplicity dimensions dA λ > 0, and a unitary matrix schur with schur ρ^{⊗t}(g) schur† = ⨁_λ ρ_λ(g) ⊗ I; reason: the paper's Schur transform is any such family; stating the result for every choice covers the paper's choice, and the operators depend on it only through its blocks
--   - encoding: the Peter–Weyl Fourier transform F on L²(G), Γ_t on all blocks λ ∈ Ĝ and the subspace F⁻¹(Tab_t) → Γ_t on Tab_t only, fourierTrunc (the coefficients ⟪F⁻¹|λ,X,Y⟩, f⟫ for λ ∈ Ĝ_t, i.e. F followed by the projection onto Tab_t) and matrixCoeffSpace (the span of F⁻¹|λ,X,Y⟩ = √d_λ⟨Y|ρ_λ(·)|X⟩, λ ∈ Ĝ_t); reason: F is unitary with F⁻¹|λ,X,Y⟩ given by Definition 3.7, and Γ_t vanishes off Tab_t, so Γ_t·F = Γ_t·fourierTrunc and F⁻¹(Tab_t) is that span; same instances
--   - encoding: V ⊗ L²(G) with Q_ρ(|x⟩⊗|f⟩) = ∫ f(g) ρ(g)|x⟩⊗|g⟩ dg → Fin N → Lp ℂ 2 μ, with (Q_ρ φ)_y = Σ_x ⟨y|ρ(·)|x⟩ · φ_x (multiplication by the continuous matrix entries as L^∞ functions); reason: (4.1) extended linearly; V ⊗ L²(G) ≅ L²(G)^N
--   - generalization: an adaptive algorithm with query register V started from |0⟩ → any finite workspace, any unitaries and any start vector ψ; reason: the source's algorithms are among these
--   - reading: "its recording register always remains in Im(Θ_t)" → after each query i, every component of the state (one per basis state of V ⊗ B) lies in Im(Θ_i) and in F⁻¹(Tab_i); reason: between queries the adversary's unitary only forms linear combinations of these components, so they stay in the same subspace
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Lemma 5.7, p.67

import Mathlib
import Definitions.Def_PathRecording_adversary

set_option autoImplicit false

namespace PathRecording

open Matrix MeasureTheory

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Lemma 5.7 (Reachable states are in `Im(Θ_t)`), p.67: "Fix any adaptive quantum
algorithm whose query register is `V` and queries `Q_ρ`. Then, its recording register always remains
in `Im(Θ_t) = F⁻¹(Tab_t)`." For every workspace `B`, unitaries `A`, start state `ψ`, number of
queries `i` and basis state `k` of `A ⊗ B`, the `k`-component of the uncompressed state after `i`
queries lies in `Im(Θ_i)` and in `F⁻¹(Tab_i)` for every Schur–Weyl data at `i`.

**Formalization Note.** "Adaptive" means that the adversary's unitaries act between queries
(see the `adversary` definitions); `F⁻¹(Tab_i)` is `matrixCoeffSpace μ S`. -/
theorem lemma_5_7 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {N : ℕ} (ρ : UnitaryRep G N) (B : Type) [Fintype B] [DecidableEq B]
    (A : ℕ → Matrix.unitaryGroup (Fin N × B) ℂ) (ψ : Fin N × B → ℂ) (i : ℕ) (k : Fin N × B) :
    uncompressedRun μ B ρ A ψ i k ∈ Set.range (theta μ ρ i) ∧
    ∀ S : SchurWeylData ρ i, uncompressedRun μ B ρ A ψ i k ∈ matrixCoeffSpace μ S := by sorry

end PathRecording
