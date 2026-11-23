-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__map_238ef0722272
-- name    : P2M_GlobalTheory_valAt__map_238ef0722272
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:03.213594+00:00
-- url     : https://prove2.me/theorems/5ed250b9-f1a6-4e0e-aefa-33c4fb1a1e2d
-- title:
--   P2 M Global Theory val At  map 238ef0722272: P2 M Global Theory val At  map 238ef0722272
-- statement:
--   The P2 M Global Theory val At  map 238ef0722272 construction uses the P2 M Global Theory val At  map 238ef0722272 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L142-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L142-L146

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
variable {X Y : Scheme.{0}}

theorem P2M_GlobalTheory_valAt__map_238ef0722272 (x : Sp ℂ ⟶ X) {U V : X.Opens} (i : Opposite.op U ⟶ Opposite.op V) (f : Γ(X, U))
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((X.presheaf.map i).hom f) = valAt' x U f := by sorry

alias «GlobalTheory».«valAt'_map» := P2M_GlobalTheory_valAt__map_238ef0722272
