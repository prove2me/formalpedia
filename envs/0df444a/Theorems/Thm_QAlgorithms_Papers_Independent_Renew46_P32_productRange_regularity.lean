-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_productRange_regularity
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.productRange_regularity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:10:12.381986+00:00
-- url     : https://prove2.me/theorems/2fc3edae-ff21-44ba-b56b-1c222b7d9676
-- title:
--   Coordinate testing in arbitrary products
-- statement:
--   Let $K$ be a Hausdorff nondiscrete topological field, $E$ and $(F_i)_{i\in I}$ be Hausdorff topological $K$-vector spaces, and $U\subseteq E$ be open. Equip $P=\prod_{i\in I}F_i$ with the product topology. For $r\in\mathbb N_0\cup\{\infty\}$ and $f:U\to P$,
--   $$f\in C^r(U,P)\quad\Longleftrightarrow\quad\operatorname{pr}_i\circ f\in C^r(U,F_i)\ \text{for every }i\in I.$$
--
--   The index set may be empty, in which case the product is the zero vector space. This is a coordinatewise regularity criterion.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 49, Lemma 10.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

/-- Lemma 10.2, PDF p. 49: arbitrary, possibly empty, product with its
product topology and its actual coordinate projections. -/
theorem productRange_regularity
    {K : Type} [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [T2Space K] (hNonDiscrete : ¬ DiscreteTopology K)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E]
    {I : Type u} {F : I → Type u}
    [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
    [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalAddGroup (F i)]
    [∀ i, ContinuousSMul K (F i)] [∀ i, T2Space (F i)]
    (U : Set E) (hU : IsOpen U) (f : E → ∀ i, F i) (r : WithTop ℕ) :
    fieldCr (K := K) r U f ↔ ∀ i, fieldCr (K := K) r U (fun x => f x i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P32
