-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P35_compactSemisimple_lie_iff_locallyContractible
-- name    : QAlgorithms.Papers.Independent.Next46.P35.compactSemisimple_lie_iff_locallyContractible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:34:44.676018+00:00
-- url     : https://prove2.me/theorems/8ff9ed7c-8a46-44b6-87e1-fd76d062b58b
-- title:
--   Compact connected semisimple groups: Lie structure and local contractibility
-- statement:
--   Let $S$ be a connected compact Hausdorff topological group that is semisimple in compact-group structure theory, meaning that its center is totally disconnected. Then
--
--   $$
--   S\text{ admits a compatible locally convex smooth Lie group structure}
--   \quad\Longleftrightarrow\quad
--   S\text{ is locally contractible at }1.
--   $$
--
--   Local contractibility means that some identity neighborhood contracts to $1$ in $S$. No finite-dimensionality or pre-existing Lie algebra is assumed in the semisimplicity condition. This gives the semisimple compact case of the paper's topological criterion.
-- source:
--   Pro-Lie groups which are infinite-dimensional Lie groups, arXiv:math/0609684v1, PDF p. 10, Proposition 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

namespace QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology

open scoped Manifold ContDiff

universe u v w z

/-- Proposition 3.4, PDF p. 10: compact semisimplicity is a group-theoretic
condition, with no assumed finite-dimensional Lie algebra. -/
theorem compactSemisimple_lie_iff_locallyContractible
    (S : Type u) [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
    [T2Space S] [CompactSpace S] [ConnectedSpace S]
    (hSemisimple : CompactGroupSemisimple S) :
    CarriesLocallyConvexLieStructure S ↔ AmbientLocallyContractibleAt (1 : S) := by sorry

end QAlgorithms.Papers.Independent.Next46.P35
