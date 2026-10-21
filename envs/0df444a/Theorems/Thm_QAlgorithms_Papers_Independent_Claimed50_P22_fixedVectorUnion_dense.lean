-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_fixedVectorUnion_dense
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.fixedVectorUnion_dense
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:11:27.752063+00:00
-- url     : https://prove2.me/theorems/ad89eb29-048f-4586-a6c8-058bc8479b92
-- title:
--   Density of the union of fixed-vector spaces
-- statement:
--   Let $G$ be a topological group, and let $(N_i)_{i\in I}$ be a nonempty downward-directed family of closed normal subgroups, cofinal in the identity neighborhoods: every identity neighborhood contains some $N_i$. Let $\pi$ be a jointly continuous unitary representation on a real or complex Hilbert space $H$. For $H^{N_i}=\{v:\pi(n)v=v\text{ for all }n\in N_i\}$, every $H^{N_i}$ is closed and $G$-invariant, and
--
--   $$\overline{\bigcup_{i\in I}H^{N_i}}=H.$$
--
--   The union itself is dense. No Lie structure or countability of the subgroup family is required.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 36, Lemma 12.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

section SubgroupFilters

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {I : Type v}

variable {K : Type w} [RCLike K]

variable {H : Type z} [NormedAddCommGroup H] [InnerProductSpace K H]

/-- Lemma 12.1, PDF p. 36: the union itself is dense. Every constituent
fixed-vector space is closed and G-invariant. No Lie structure is assumed. -/
theorem fixedVectorUnion_dense [CompleteSpace H]
    (N : I → Subgroup G) (hN : NormalSubgroupFilter N)
    (pi : G →* (H ≃ₗᵢ[K] H))
    (hContinuous : Continuous (fun p : G × H => pi p.1 p.2)) :
    (∀ i, IsClosed (FixedVectors pi (N i))) ∧
    (∀ i g v, v ∈ FixedVectors pi (N i) → pi g v ∈ FixedVectors pi (N i)) ∧
    Dense (⋃ i, FixedVectors pi (N i)) := by sorry

end SubgroupFilters

end QAlgorithms.Papers.Independent.Claimed50.P22
