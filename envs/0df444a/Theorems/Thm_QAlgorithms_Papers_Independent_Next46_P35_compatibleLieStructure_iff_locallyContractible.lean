-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P35_compatibleLieStructure_iff_locallyContractible
-- name    : QAlgorithms.Papers.Independent.Next46.P35.compatibleLieStructure_iff_locallyContractible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:34:08.461665+00:00
-- url     : https://prove2.me/theorems/86d00b9f-fe9c-49b8-8507-d3121d8e7c57
-- title:
--   Pro-Lie groups admit compatible Lie structures exactly when locally contractible
-- statement:
--   Let $G$ be a Hausdorff topological pro-Lie group: it is topologically isomorphic to a closed subgroup of an arbitrary product of finite-dimensional real Lie groups. Then
--
--   $$
--   G\text{ admits a compatible locally convex smooth Lie group structure}
--   \quad\Longleftrightarrow\quad
--   \exists U\in\mathcal N_G(1),\; (U\hookrightarrow G)\simeq(U\to\{1\}).
--   $$
--
--   The homotopy contracts the inclusion to the constant map with value $1$ in the ambient space $G$. A compatible Lie structure uses the given topology, an arbitrary Hausdorff locally convex real model, and smooth multiplication and inversion. No regularity or exponential function is assumed. This is an existence criterion; it does not identify every given compatible smooth structure.
-- source:
--   Pro-Lie groups which are infinite-dimensional Lie groups, arXiv:math/0609684v1, PDF p. 3, Theorem 1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

namespace QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology

open scoped Manifold ContDiff

universe u v w z

/-- Theorem 1.1, PDF pp. 1,3: existence, rather than uniqueness, of a
compatible locally convex smooth Lie group structure on a pro-Lie group. -/
theorem compatibleLieStructure_iff_locallyContractible
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (hProLie : IsProLieGroup G) :
    CarriesLocallyConvexLieStructure G ↔ AmbientLocallyContractibleAt (1 : G) := by sorry

end QAlgorithms.Papers.Independent.Next46.P35
