-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P35_finitelyGenerated_integerProduct_discrete
-- name    : QAlgorithms.Papers.Independent.Next46.P35.finitelyGenerated_integerProduct_discrete
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:37:16.736932+00:00
-- url     : https://prove2.me/theorems/511b3d6b-915d-438d-9a42-5fd76defe582
-- title:
--   Finitely generated subgroups of arbitrary integer products are discrete
-- statement:
--   Let $J$ be any set and give $\mathbb Z^J$ the product topology, where each copy of $\mathbb Z$ is discrete. For every finitely generated additive subgroup $D\le\mathbb Z^J$,
--
--   $$
--   D\text{ is discrete in the induced topology.}
--   $$
--
--   The product includes all functions $J\to\mathbb Z$, without a finite-support requirement. The empty index set and the trivial subgroup are allowed. This result detects discreteness from algebraic finite generation in an arbitrary product.
-- source:
--   Pro-Lie groups which are infinite-dimensional Lie groups, arXiv:math/0609684v1, PDF p. 22, Lemma 5.12

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

namespace QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology

open scoped Manifold ContDiff

universe u v w z

/-- Lemma 5.12, PDF pp. 22–23: the full integer product has the product
topology. J may be empty, and no finite-support condition is imposed. -/
theorem finitelyGenerated_integerProduct_discrete
    {J : Type u} (D : AddSubgroup (J → ℤ)) (hFG : D.FG) :
    DiscreteTopology D := by sorry

end QAlgorithms.Papers.Independent.Next46.P35
