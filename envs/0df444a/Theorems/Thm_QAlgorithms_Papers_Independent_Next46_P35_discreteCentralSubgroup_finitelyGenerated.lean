-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P35_discreteCentralSubgroup_finitelyGenerated
-- name    : QAlgorithms.Papers.Independent.Next46.P35.discreteCentralSubgroup_finitelyGenerated
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:36:40.874268+00:00
-- url     : https://prove2.me/theorems/2a255cbf-5986-4e78-98c6-5d91dfa7aa06
-- title:
--   Discrete central subgroups of connected pro-Lie groups are finitely generated
-- statement:
--   Let $G$ be a connected Hausdorff topological pro-Lie group and let $D\le Z(G)$ be a subgroup that is discrete in the topology induced from $G$. Then
--
--   $$
--   D\text{ is finitely generated as an abstract group.}
--   $$
--
--   This supplies the finite-generation necessity in the later discreteness criterion for centers of universal pro-Lie groups.
--
--   **Source correction.** The printed lemma omits connectedness. It is restored here, as required by the connected finite-dimensional fact explicitly used in footnote 1 on p. 22 and by the later applications to $\Gamma(\mathfrak g)$. Without it, an infinite-rank discrete free abelian group is a counterexample. Independent moderation of this correction remains pending.
-- source:
--   Pro-Lie groups which are infinite-dimensional Lie groups, arXiv:math/0609684v1, PDF p. 21, Lemma 5.10

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

namespace QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology

open scoped Manifold ContDiff

universe u v w z

/-- Lemma 5.10, PDF pp. 21–22, corrected by restoring connectedness, used
explicitly in footnote 1 on p. 22. The printed version is false for a discrete
free abelian group of infinite rank. This correction requires independent moderation. -/
theorem discreteCentralSubgroup_finitelyGenerated
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [ConnectedSpace G] (hProLie : IsProLieGroup G)
    (D : Subgroup G) (hCentral : D ≤ Subgroup.center G)
    (hDiscrete : DiscreteTopology D) : D.FG := by sorry

end QAlgorithms.Papers.Independent.Next46.P35
