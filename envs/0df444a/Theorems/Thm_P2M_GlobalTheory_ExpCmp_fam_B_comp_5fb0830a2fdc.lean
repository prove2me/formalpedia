-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ExpCmp_fam_B_comp_5fb0830a2fdc
-- name    : P2M_GlobalTheory_ExpCmp_fam_B_comp_5fb0830a2fdc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:29:45.704975+00:00
-- url     : https://prove2.me/theorems/7277c39d-fef3-4fff-bc82-44c01eec8e09
-- title:
--   P2 M Global Theory Exp Cmp fam B comp 5fb0830a2fdc: P2 M Global Theory Exp Cmp fam B comp 5fb0830a2fdc
-- statement:
--   The P2 M Global Theory Exp Cmp fam B comp 5fb0830a2fdc construction uses the P2 M Global Theory Exp Cmp fam B comp 5fb0830a2fdc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitMapSnd.lean#L43-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitMapSnd.lean#L43-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitMapSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

theorem P2M_GlobalTheory_ExpCmp_fam_B_comp_5fb0830a2fdc {φ : R →+* V} {D : DegPre R} {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left}
    (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {α' : D'.X} {α : D.X}
    (hc : (D'.c α').left ≫ β = spMap φ ≫ (D.c α).left) (i : Fin 4) :
    D'.famφB α' i ≫ β = β ≫ D.famφB α i := by sorry

alias «GlobalTheory».«ExpCmp».«famφB_comp» := P2M_GlobalTheory_ExpCmp_fam_B_comp_5fb0830a2fdc
