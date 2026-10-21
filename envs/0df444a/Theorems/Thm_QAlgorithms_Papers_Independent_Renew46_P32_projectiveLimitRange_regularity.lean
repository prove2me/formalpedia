-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_projectiveLimitRange_regularity
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.projectiveLimitRange_regularity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:10:45.06052+00:00
-- url     : https://prove2.me/theorems/771e942e-3f3f-4cc0-80a2-4ba54c2ec609
-- title:
--   Coordinate testing in a projective limit
-- statement:
--   Let $K$ be a Hausdorff nondiscrete topological field and let $(F_i,\phi_{ij})$ be a projective system of Hausdorff topological $K$-vector spaces over a directed preorder $I$. The bonding maps $\phi_{ij}:F_j\to F_i$ are continuous and linear and satisfy the identity and composition laws. Let
--   $$F=\{(z_i)\in\prod_i F_i:\phi_{ij}(z_j)=z_i\text{ for }i\le j\}$$
--   with its subspace topology and canonical projections $\pi_i$. If $U$ is open in a Hausdorff topological $K$-vector space $E$, $f:U\to F$, and $r\in\mathbb N_0\cup\{\infty\}$, then $f$ is $C^r$ if and only if every $\pi_i\circ f$ is $C^r$.
--
--   This tests regularity in the actual inverse-limit space; bonding maps need not be surjective.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 49, Lemma 10.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

/-- Lemma 10.3, PDF p. 49: coordinate testing in the actual inverse limit,
with the subspace topology, for all finite orders and infinity. -/
theorem projectiveLimitRange_regularity
    {K : Type} [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [T2Space K] (hNonDiscrete : ¬ DiscreteTopology K)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E]
    {I : Type u} [Preorder I] [IsDirectedOrder I]
    {F : I → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
    [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalAddGroup (F i)]
    [∀ i, ContinuousSMul K (F i)] [∀ i, T2Space (F i)]
    (bond : ∀ i j : I, i ≤ j → F j →ₗ[K] F i)
    (hCont : ∀ i j h, Continuous (bond i j h))
    (hId : ∀ i, bond i i le_rfl = LinearMap.id)
    (hComp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      bond i k (le_trans hij hjk) = (bond i j hij).comp (bond j k hjk))
    (U : Set E) (hU : IsOpen U) (f : E → projectiveLimitSubmodule bond)
    (r : WithTop ℕ) :
    fieldCr (K := K) r U f ↔
      ∀ i, fieldCr (K := K) r U (fun x => (f x).val i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P32
