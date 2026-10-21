-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_irreducibleUnitaryRepresentation_factors
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.irreducibleUnitaryRepresentation_factors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:12:37.596782+00:00
-- url     : https://prove2.me/theorems/ed7f43e8-6d10-422b-a9b3-51173c8bbce3
-- title:
--   Factorization of irreducible unitary representations
-- statement:
--   Let $G$ and $(N_i)_{i\in I}$ satisfy the subgroup-filter assumptions of Section 12. Let $\pi$ be a jointly continuous irreducible unitary representation on a nonzero real or complex Hilbert space $H$, where irreducible means that the only closed invariant linear subspaces are $\{0\}$ and $H$. Then
--
--   $$\exists i\in I\ \exists\overline\pi:G/N_i\to U(H):\quad \pi=\overline\pi\circ q_i,$$
--
--   where $q_i$ is the quotient homomorphism and $\overline\pi$ has a jointly continuous unitary action. This is the factorization form of the source's equality of unitary duals and requires no choice of representatives of equivalence classes.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 36, Corollary 12.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

section SubgroupFilters

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {I : Type v}

variable {K : Type w} [RCLike K]

variable {H : Type z} [NormedAddCommGroup H] [InnerProductSpace K H]

/-- Corollary 12.3, PDF p. 36: every nonzero irreducible continuous
unitary representation factors continuously through one quotient. The
factorization avoids choices of representatives in the unitary dual. -/
theorem irreducibleUnitaryRepresentation_factors [CompleteSpace H] [Nontrivial H]
    (N : I → Subgroup G) [∀ i, (N i).Normal]
    (hN : NormalSubgroupFilter N)
    (pi : G →* (H ≃ₗᵢ[K] H))
    (hContinuous : Continuous (fun p : G × H => pi p.1 p.2))
    (hIrreducible : ∀ S : Submodule K H,
      IsClosed (S : Set H) →
      (∀ g v, v ∈ S → pi g v ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∃ i, ∃ rho : (G ⧸ N i) →* (H ≃ₗᵢ[K] H),
      Continuous (fun p : (G ⧸ N i) × H => rho p.1 p.2) ∧
      (∀ g : G, rho (QuotientGroup.mk g) = pi g) := by sorry

end SubgroupFilters

end QAlgorithms.Papers.Independent.Claimed50.P22
