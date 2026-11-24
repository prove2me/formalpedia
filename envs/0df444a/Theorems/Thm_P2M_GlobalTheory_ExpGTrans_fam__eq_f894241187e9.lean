-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ExpGTrans_fam__eq_f894241187e9
-- name    : P2M_GlobalTheory_ExpGTrans_fam__eq_f894241187e9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:10.813569+00:00
-- url     : https://prove2.me/theorems/6145fd38-918f-4a85-80cd-2a8e7a64b546
-- title:
--   P2 M Global Theory Exp GTrans fam  eq f894241187e9: P2 M Global Theory Exp GTrans fam  eq f894241187e9
-- statement:
--   The P2 M Global Theory Exp GTrans fam  eq f894241187e9 construction uses the P2 M Global Theory Exp GTrans fam  eq f894241187e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsGTransport.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsGTransport.lean#L129-L140

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsGTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ExpGTrans
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {D : DegPre R} {D' : DegPre R'}

theorem P2M_GlobalTheory_ExpGTrans_fam__eq_f894241187e9 (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (α : D.X) (κ : Fin 4) :
    DegPre.famφ D F α κ = (DegPre.prB D F).left ≫ D.famφB α κ := by sorry

alias «GlobalTheory».«ExpGTrans».«famφ_eq» := P2M_GlobalTheory_ExpGTrans_fam__eq_f894241187e9
