-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_unitaryRepresentation_decomposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.unitaryRepresentation_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:12:05.987219+00:00
-- url     : https://prove2.me/theorems/a6e0c7e7-1a18-4950-826b-37dbc2769d83
-- title:
--   Hilbert direct-sum decomposition through subgroup quotients
-- statement:
--   Let $G$ be a topological group and $(N_i)_{i\in I}$ a nonempty downward-directed family of closed normal subgroups cofinal in its identity neighborhoods. Every jointly continuous unitary representation $\pi$ on a real or complex Hilbert space $H$ has an orthogonal Hilbert direct-sum decomposition
--
--   $$H=\widehat{\bigoplus}_{j\in J}H_j,\qquad \forall j\in J\ \exists i\in I:\quad \pi(N_i)|_{H_j}=1.$$
--
--   Each $H_j$ is closed and $G$-invariant. Equivalently, the summands are pairwise orthogonal and their algebraic sum is dense. The subgroup index may depend on the summand, and the zero Hilbert space and empty sum are allowed.
--
--   **Formalization Note** Unitarity is restored from Section 12's standing convention and its use of invariant orthogonal complements in the proof.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 36, Theorem 12.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

section SubgroupFilters

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {I : Type v}

variable {K : Type w} [RCLike K]

variable {H : Type z} [NormedAddCommGroup H] [InnerProductSpace K H]

/-- Theorem 12.2, PDF p. 36: an orthogonal Hilbert direct-sum
realization by closed invariant subspaces, with a possibly different
subgroup acting trivially on each summand. Unitarity is restored from the
section's standing hypothesis. -/
theorem unitaryRepresentation_decomposition [CompleteSpace H]
    (N : I → Subgroup G) (hN : NormalSubgroupFilter N)
    (pi : G →* (H ≃ₗᵢ[K] H))
    (hContinuous : Continuous (fun p : G × H => pi p.1 p.2)) :
    ∃ (J : Type z) (S : J → Submodule K H),
      (∀ j, IsClosed (S j : Set H)) ∧
      (∀ j g v, v ∈ S j → pi g v ∈ S j) ∧
      (∀ j k, j ≠ k → ∀ v ∈ S j, ∀ w ∈ S k, inner K v w = 0) ∧
      (Dense (Submodule.span K (⋃ j, (S j : Set H)) : Set H)) ∧
      (∀ j, ∃ i, ∀ g ∈ N i, ∀ v ∈ S j, pi g v = v) := by sorry

end SubgroupFilters

end QAlgorithms.Papers.Independent.Claimed50.P22
