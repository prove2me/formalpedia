-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P35_compactAbelian_lie_iff_locallyContractible
-- name    : QAlgorithms.Papers.Independent.Next46.P35.compactAbelian_lie_iff_locallyContractible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:35:23.118221+00:00
-- url     : https://prove2.me/theorems/273a8944-289b-4ce4-97dd-20140e293055
-- title:
--   Compact connected abelian groups: Lie structure and local contractibility
-- statement:
--   Let $A$ be a connected compact Hausdorff abelian topological group. Then
--
--   $$
--   A\text{ admits a compatible locally convex smooth Lie group structure}
--   \quad\Longleftrightarrow\quad
--   \exists U\in\mathcal N_A(1),\; (U\hookrightarrow A)\simeq(U\to\{1\}).
--   $$
--
--   The homotopy takes place in $A$ and may leave $U$. The Lie structure must induce exactly the original topology. This is the abelian compact case of the paper's characterization.
-- source:
--   Pro-Lie groups which are infinite-dimensional Lie groups, arXiv:math/0609684v1, PDF p. 10, Proposition 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

namespace QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology

open scoped Manifold ContDiff

universe u v w z

/-- Proposition 3.5, PDF pp. 10–11: connected compact abelian groups.
The conclusion is existence of a compatible structure, not a structure fixed in advance. -/
theorem compactAbelian_lie_iff_locallyContractible
    (A : Type u) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] [ConnectedSpace A] :
    CarriesLocallyConvexLieStructure A ↔ AmbientLocallyContractibleAt (1 : A) := by sorry

end QAlgorithms.Papers.Independent.Next46.P35
