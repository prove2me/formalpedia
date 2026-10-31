-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_groupObjectsInTop
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.groupObjectsInTop
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:27:53.031638+00:00
-- url     : https://prove2.me/theorems/faa1da16-05c2-450e-b5d4-02bf9e7f702a
-- title:
--   Group objects in Top are topological groups
-- statement:
--   Fix a topological space $G$ and maps $m:G\times G\to G$, $e\in G$, and $i:G\to G$. They form a group object in Top exactly when the group structure computed from those same maps is a topological group. Explicitly the required continuity is
--
--   $$m\text{ is continuous on }G\times G,\qquad i\text{ is continuous on }G.$$
--
--   The algebraic requirements are associativity, both unit laws for $e$, and both inverse laws for $i$. The constant identity map from the one-point space is continuous. This correspondence preserves the topology and every operation, without any separation or compactness assumption.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 3, §1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 3: group objects in Top are precisely topological groups, with
identical topology and operations. No separation axiom is imposed. -/
theorem groupObjectsInTop {G : Type u} [TopologicalSpace G] (D : GroupMaps G) :
    GroupObjectInTop D ↔
      ∃ h : GroupDiagrams D,
        letI : Group G := groupOfMaps D h
        IsTopologicalGroup G := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
