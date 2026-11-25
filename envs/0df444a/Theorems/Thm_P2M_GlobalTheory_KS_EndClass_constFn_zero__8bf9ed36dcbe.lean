-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KS_EndClass_constFn_zero__8bf9ed36dcbe
-- name    : P2M_GlobalTheory_KS_EndClass_constFn_zero__8bf9ed36dcbe
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:32.251251+00:00
-- url     : https://prove2.me/theorems/64820489-edc8-4758-abe6-dfc6e4e57e39
-- title:
--   P2 M Global Theory KS End Class const Fn zero  8bf9ed36dcbe: P2 M Global Theory KS End Class const Fn zero  8bf9ed36dcbe
-- statement:
--   The P2 M Global Theory KS End Class const Fn zero  8bf9ed36dcbe construction uses the P2 M Global Theory KS End Class const Fn zero  8bf9ed36dcbe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L52-L53

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

theorem P2M_GlobalTheory_KS_EndClass_constFn_zero__8bf9ed36dcbe {R : Type} [CommRing R] (q : Y ⟶ Sp R) (O : Y.Opens) : constFn q O 0 = 0 := by sorry

alias «GlobalTheory».«KS».«EndClass».«constFn_zero'» := P2M_GlobalTheory_KS_EndClass_constFn_zero__8bf9ed36dcbe
