-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P35_compact_locallyContractible_carriesLieStructure
-- name    : QAlgorithms.Papers.Independent.Next46.P35.compact_locallyContractible_carriesLieStructure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:36:04.659064+00:00
-- url     : https://prove2.me/theorems/d63e008a-221d-4184-b522-8da43f043e94
-- title:
--   Connected compact locally contractible groups admit Lie structures
-- statement:
--   Let $G$ be a connected compact Hausdorff topological group. Suppose that an identity neighborhood contracts to $1$ in the ambient group $G$. Then
--
--   $$
--   G\text{ admits a smooth Lie group structure compatible with its topology.}
--   $$
--
--   Here a Lie structure is modelled on a Hausdorff locally convex real space, with smooth group operations. This conclusion supplies a smooth structure; none is part of the hypothesis.
-- source:
--   Pro-Lie groups which are infinite-dimensional Lie groups, arXiv:math/0609684v1, PDF p. 11, Corollary 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

namespace QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology

open scoped Manifold ContDiff

universe u v w z

/-- Corollary 3.6, PDF p. 11: connected compact locally contractible groups
admit a compatible locally convex smooth Lie group structure. -/
theorem compact_locallyContractible_carriesLieStructure
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [ConnectedSpace G]
    (hLocal : AmbientLocallyContractibleAt (1 : G)) :
    CarriesLocallyConvexLieStructure G := by sorry

end QAlgorithms.Papers.Independent.Next46.P35
