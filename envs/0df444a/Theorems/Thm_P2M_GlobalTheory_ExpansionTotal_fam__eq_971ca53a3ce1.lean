-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ExpansionTotal_fam__eq_971ca53a3ce1
-- name    : P2M_GlobalTheory_ExpansionTotal_fam__eq_971ca53a3ce1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:34.548956+00:00
-- url     : https://prove2.me/theorems/98334e87-41cc-4d86-882c-c1bcd3ecf15f
-- title:
--   P2 M Global Theory Expansion Total fam  eq 971ca53a3ce1: P2 M Global Theory Expansion Total fam  eq 971ca53a3ce1
-- statement:
--   The P2 M Global Theory Expansion Total fam  eq 971ca53a3ce1 construction uses the P2 M Global Theory Expansion Total fam  eq 971ca53a3ce1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecLinOfSecScal.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecLinOfSecScal.lean#L38-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecLinOfSecScal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExpansionTotal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)

theorem P2M_GlobalTheory_ExpansionTotal_fam__eq_971ca53a3ce1 (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (toBK θ D).left ≫ DegPre.famφ D F' α i := by sorry

alias «GlobalTheory».«ExpansionTotal».«famφ_eq» := P2M_GlobalTheory_ExpansionTotal_fam__eq_971ca53a3ce1
