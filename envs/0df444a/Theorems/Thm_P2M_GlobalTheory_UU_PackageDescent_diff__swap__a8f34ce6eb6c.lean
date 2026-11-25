-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UU_PackageDescent_diff__swap__a8f34ce6eb6c
-- name    : P2M_GlobalTheory_UU_PackageDescent_diff__swap__a8f34ce6eb6c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:01:23.393364+00:00
-- url     : https://prove2.me/theorems/868efe2e-18ec-535d-844c-ed846c65c298
-- title:
--   P2 M Global Theory UU Package Descent diff  swap  a8f34ce6eb6c: P2 M Global Theory UU Package Descent diff  swap  a8f34ce6eb6c
-- statement:
--   The P2 M Global Theory UU Package Descent diff  swap  a8f34ce6eb6c construction uses the P2 M Global Theory UU Package Descent diff  swap  a8f34ce6eb6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDescendThrough.lean#L261-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDescendThrough.lean#L261-L266

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
variable [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] [IsMonHom q] [QuasiCompact q.left]

theorem P2M_GlobalTheory_UU_PackageDescent_diff__swap__a8f34ce6eb6c {A U : Type} [CommGroup A] [CommGroup U] (W : A → U) (a b d : A) :
    diff₃ W a b d = diff₃ W a d b := by sorry

alias «GlobalTheory».«UU».«PackageDescent».«diff₃_swap₂» := P2M_GlobalTheory_UU_PackageDescent_diff__swap__a8f34ce6eb6c
