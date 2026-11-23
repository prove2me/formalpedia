-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeightGen_comp_O__ce33ccf541f8
-- name    : P2M_GlobalTheory_WeightGen_comp_O__ce33ccf541f8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:13.959003+00:00
-- url     : https://prove2.me/theorems/3b2d76a9-692e-41d5-b603-8dc7ff794b4e
-- title:
--   P2 M Global Theory Weight Gen comp O  ce33ccf541f8: P2 M Global Theory Weight Gen comp O  ce33ccf541f8
-- statement:
--   The P2 M Global Theory Weight Gen comp O  ce33ccf541f8 construction uses the P2 M Global Theory Weight Gen comp O  ce33ccf541f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L357-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L357-L367

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem P2M_GlobalTheory_WeightGen_comp_O__ce33ccf541f8 {T T' : Over (Spec (CommRingCat.of R))} (h : T' ⟶ T) (p : T ⟶ D.P.A) (χ : D.X)
    (k : Fin 4) : h.left ≫ D.Oφ p χ k = D.Oφ (h ≫ p) χ k := by sorry

alias «GlobalTheory».«WeightGen».«comp_Oφ» := P2M_GlobalTheory_WeightGen_comp_O__ce33ccf541f8
