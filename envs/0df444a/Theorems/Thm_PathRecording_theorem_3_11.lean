-- Prove2me | Theorems.Thm_PathRecording_theorem_3_11
-- name    : PathRecording.theorem_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:35.915291+00:00
-- url     : https://prove2.me/theorems/64a503cc-f250-478a-b94c-430598401e76
-- title:
--   Theorem 3.11 — Schur–Weyl duality for a unitary representation of a compact group
-- statement:
--   Let $G$ be a compact group and $\rho:G\to U(N)$ a continuous unitary representation, and let $t\ge0$. Let $\mathcal A_t$ be the commutant algebra of $\rho^{\otimes t}$. Then:
--
--   1. $V^{\otimes t}$ decomposes as $V^{\otimes t}\simeq\bigoplus_\lambda V^\lambda_G\otimes V^\lambda_{\mathcal A_t}$ with each $V^\lambda_G$ an irreducible representation of $G$ and
--   $$\rho^{\otimes t}(g)=\bigoplus_\lambda\rho_\lambda(g)\otimes I_{V^\lambda_{\mathcal A_t}}$$
--   (Schur–Weyl data exist);
--   2. for every such decomposition, each $X\in\mathcal A_t$ acts as $X=\bigoplus_\lambda I_{V^\lambda_G}\otimes\rho_\lambda(X)$;
--   3. each $V^\lambda_{\mathcal A_t}$ is an irreducible representation of $\mathcal A_t$: the only subspaces invariant under all $\rho_\lambda(X)$, $X\in\mathcal A_t$, are $0$ and $V^\lambda_{\mathcal A_t}$;
--   4. the commutant of $\mathcal A_t$ is
--   $$\mathrm{End}_{\mathcal A_t}(V^{\otimes t})=\mathrm{Span}\{\rho(g)^{\otimes t}\}_{g\in G}.$$
--
--   This makes the Schur transform, on which the path-recording oracle is built, available for every number of queries.
--
--   Differences from the source:
--   - generalization: G a compact Lie group → G any compact topological group; reason: the Lie structure is not used; a compact Lie group is a compact topological group
--   - generalization: t ≥ 1 (Definition 3.10) → every t ∈ ℕ, including t = 0; reason: at t = 0 there is one trivial block; the source's t ≥ 1 cases are included
--   - generalization: the action of 𝒜_t "under this decomposition" → clauses 2 and 3 for every Schur–Weyl decomposition; reason: every such decomposition is one the theorem refers to; the source's decomposition is included
--   - encoding: V^{⊗t} ≃ ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t} with V^λ_G irreducible → Nonempty (SchurWeylData ρ t), whose irreps are irreducible and pairwise inequivalent and whose multiplicity dimensions are positive; reason: distinct isomorphism classes λ are inequivalent and only labels that occur are listed; same decompositions
--   - encoding: X = ⨁_λ I ⊗ ρ_λ(X) and irreducibility of V^λ_{𝒜_t} as an 𝒜_t-representation → existence of blocks σ with Schur_t X Schur_t† = ⨁_λ I ⊗ σ λ, and every subspace invariant under all such blocks σ λ is 0 or everything; reason: ρ_λ(X) is the block σ λ, which the equation determines
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 3.11, p.34

import Mathlib
import Definitions.Def_PathRecording_SchurWeylData

set_option autoImplicit false

namespace PathRecording

open Matrix Kronecker

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 3.11 (Schur–Weyl duality), p.34. Let `G` be a compact group and
`ρ : G → U(N)` a continuous unitary representation, `t ∈ ℕ`. Then:
1. `V^{⊗t} ≃ ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t}` with `V^λ_G` irreducible and `ρ^{⊗t}(g) = ⨁_λ ρ_λ(g) ⊗ I`
   (Schur–Weyl data exist);
2. under any such decomposition every `X ∈ 𝒜_t` acts as `⨁_λ I_{V^λ_G} ⊗ ρ_λ(X)`;
3. each `V^λ_{𝒜_t}` is an irreducible representation of `𝒜_t` (no subspace other than `0` and the
   whole space is invariant under every `ρ_λ(X)`, `X ∈ 𝒜_t`);
4. `End_{𝒜_t}(V^{⊗t}) = Span{ρ(g)^{⊗t}}_{g∈G}`.

**Formalization Note.** `t = 0` is included (the paper's Definition 3.10 takes `t ≥ 1`; at `t = 0`
the statement holds with one trivial block). Clause 2 is stated for every Schur–Weyl data, so `ρ_λ(X)`
is the block `σ λ` with `Schur_t X Schur_t† = ⨁_λ I ⊗ σ λ`; clause 3 quantifies over those blocks. -/
theorem theorem_3_11 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] {N : ℕ} (ρ : UnitaryRep G N) (t : ℕ) :
    Nonempty (SchurWeylData ρ t) ∧
    (∀ S : SchurWeylData ρ t, ∀ X ∈ commutant ρ t,
      ∃ σ : (l : S.ι) → Matrix (Fin (S.dA l)) (Fin (S.dA l)) ℂ,
        S.schur * X * S.schurᴴ =
          blockDiagonal' fun l => (1 : Matrix (Fin (S.dG l)) (Fin (S.dG l)) ℂ) ⊗ₖ σ l) ∧
    (∀ S : SchurWeylData ρ t, ∀ l : S.ι, ∀ W : Submodule ℂ (Fin (S.dA l) → ℂ),
      (∀ X ∈ commutant ρ t, ∀ σ : (l : S.ι) → Matrix (Fin (S.dA l)) (Fin (S.dA l)) ℂ,
        S.schur * X * S.schurᴴ =
            (blockDiagonal' fun l => (1 : Matrix (Fin (S.dG l)) (Fin (S.dG l)) ℂ) ⊗ₖ σ l) →
          ∀ v ∈ W, σ l *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤) ∧
    {Y : Matrix (Fin t → Fin N) (Fin t → Fin N) ℂ | ∀ X ∈ commutant ρ t, Y * X = X * Y} =
      (Submodule.span ℂ (Set.range (tensorPow ρ t)) : Set (Matrix (Fin t → Fin N) (Fin t → Fin N) ℂ)) := by sorry

end PathRecording
