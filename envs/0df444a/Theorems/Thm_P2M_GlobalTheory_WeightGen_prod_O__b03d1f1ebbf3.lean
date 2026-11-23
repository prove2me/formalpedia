-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeightGen_prod_O__b03d1f1ebbf3
-- name    : P2M_GlobalTheory_WeightGen_prod_O__b03d1f1ebbf3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:01.448362+00:00
-- url     : https://prove2.me/theorems/368f09b8-4580-4d5d-b1a7-bf7f6c8600d4
-- title:
--   P2 M Global Theory Weight Gen prod O  b03d1f1ebbf3: P2 M Global Theory Weight Gen prod O  b03d1f1ebbf3
-- statement:
--   The P2 M Global Theory Weight Gen prod O  b03d1f1ebbf3 construction uses the P2 M Global Theory Weight Gen prod O  b03d1f1ebbf3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L369-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L369-L376

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

theorem P2M_GlobalTheory_WeightGen_prod_O__b03d1f1ebbf3 {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (D.Oφ p χ k) ^ Oinvε k = (h (p * (toUnit T ≫ D.c χ)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h p.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by sorry

alias «GlobalTheory».«WeightGen».«prod_Oφ» := P2M_GlobalTheory_WeightGen_prod_O__b03d1f1ebbf3
