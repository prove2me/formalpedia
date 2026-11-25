-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pre___eq_20bc979cb662
-- name    : P2M_GlobalTheory_KS_EndClass_pre___eq_20bc979cb662
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:08:45.737035+00:00
-- url     : https://prove2.me/theorems/00bdc75e-1fd7-46f8-abba-16fb24a0a5f5
-- title:
--   P2 M Global Theory KS End Class pre   eq 20bc979cb662: P2 M Global Theory KS End Class pre   eq 20bc979cb662
-- statement:
--   The P2 M Global Theory KS End Class pre   eq 20bc979cb662 construction uses the P2 M Global Theory KS End Class pre   eq 20bc979cb662 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L55-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassCohomologousAlongEndomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}

theorem P2M_GlobalTheory_KS_EndClass_pre___eq_20bc979cb662 (O : Y.Opens) (y : Y ⟶ Z) (m : Z ⟶ X) (W : X.Opens) :
    ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W = O.ι ⁻¹ᵁ (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) := by sorry

alias «GlobalTheory».«KS».«EndClass».«pre_ι_eq» := P2M_GlobalTheory_KS_EndClass_pre___eq_20bc979cb662
