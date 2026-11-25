-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorusGrading_toSpec__appLE_fromSpec_57347db5ee06
-- name    : P2M_GlobalTheory_TorusGrading_toSpec__appLE_fromSpec_57347db5ee06
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:40.148012+00:00
-- url     : https://prove2.me/theorems/836d42ca-fa53-483a-bc1c-66d549bdc343
-- title:
--   P2 M Global Theory Torus Grading to Spec  app LE from Spec 57347db5ee06: P2 M Global Theory Torus Grading to Spec  app LE from Spec 57347db5ee06
-- statement:
--   The P2 M Global Theory Torus Grading to Spec  app LE from Spec 57347db5ee06 construction uses the P2 M Global Theory Torus Grading to Spec  app LE from Spec 57347db5ee06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGraded.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGraded.lean#L21-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
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
open GlobalTheory
open GlobalTheory.TorusGrading

theorem P2M_GlobalTheory_TorusGrading_toSpec__appLE_fromSpec_57347db5ee06 {Y Z : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (g : Z ⟶ Y)
    (h : ⊤ ≤ g ⁻¹ᵁ V) : Z.toSpecΓ ≫ Spec.map (g.appLE V ⊤ h) ≫ hV.fromSpec = g := by sorry

alias «GlobalTheory».«TorusGrading».«toSpecΓ_appLE_fromSpec» := P2M_GlobalTheory_TorusGrading_toSpec__appLE_fromSpec_57347db5ee06
