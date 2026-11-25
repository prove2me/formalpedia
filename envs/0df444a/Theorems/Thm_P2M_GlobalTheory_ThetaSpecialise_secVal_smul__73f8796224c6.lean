-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaSpecialise_secVal_smul__73f8796224c6
-- name    : P2M_GlobalTheory_ThetaSpecialise_secVal_smul__73f8796224c6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:06.386864+00:00
-- url     : https://prove2.me/theorems/a32d2463-8bea-4c77-be04-bec04ae80897
-- title:
--   P2 M Global Theory Theta Specialise sec Val smul  73f8796224c6: P2 M Global Theory Theta Specialise sec Val smul  73f8796224c6
-- statement:
--   The P2 M Global Theory Theta Specialise sec Val smul  73f8796224c6 construction uses the P2 M Global Theory Theta Specialise sec Val smul  73f8796224c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsFOfIntegral.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsFOfIntegral.lean#L51-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {S₀ : Scheme.{0}} {A : Over S₀} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S₀}
  {S : Type} [CommRing S]

theorem P2M_GlobalTheory_ThetaSpecialise_secVal_smul__73f8796224c6 (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (c : S) (s : SecOver π (LPow A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal (c • s : SecOver π _) r z J = constVal (r ≫ π) z c * secVal s r z J := by sorry

alias «GlobalTheory».«ThetaSpecialise».«secVal_smul'» := P2M_GlobalTheory_ThetaSpecialise_secVal_smul__73f8796224c6
