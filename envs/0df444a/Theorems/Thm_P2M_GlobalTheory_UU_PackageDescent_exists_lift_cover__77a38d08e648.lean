-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UU_PackageDescent_exists_lift_cover__77a38d08e648
-- name    : P2M_GlobalTheory_UU_PackageDescent_exists_lift_cover__77a38d08e648
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:52:40.812618+00:00
-- url     : https://prove2.me/theorems/589c1f11-bccd-4ceb-ab86-e2697c625190
-- title:
--   P2 M Global Theory UU Package Descent exists lift cover  77a38d08e648: P2 M Global Theory UU Package Descent exists lift cover  77a38d08e648
-- statement:
--   The P2 M Global Theory UU Package Descent exists lift cover  77a38d08e648 construction uses the P2 M Global Theory UU Package Descent exists lift cover  77a38d08e648 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDescendThrough.lean#L233-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDescendThrough.lean#L233-L243

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G B : Over S} (q : G ⟶ B) [Flat q.left] [Surjective q.left]

theorem P2M_GlobalTheory_UU_PackageDescent_exists_lift_cover__77a38d08e648 {T : Over S} (x y u v : T ⟶ B) :
    ∃ (T' : Over S) (ρ : T' ⟶ T) (x' y' u' v' : T' ⟶ G), Flat ρ.left ∧ Surjective ρ.left ∧ x' ≫ q = ρ ≫ x ∧
      y' ≫ q = ρ ≫ y ∧ u' ≫ q = ρ ≫ u ∧ v' ≫ q = ρ ≫ v := by sorry

alias «GlobalTheory».«UU».«PackageDescent».«exists_lift_cover₄» := P2M_GlobalTheory_UU_PackageDescent_exists_lift_cover__77a38d08e648
