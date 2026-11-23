-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_zero__c17798940263
-- name    : P2M_GlobalTheory_FieldBaseChange_sval_zero__c17798940263
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:09.856835+00:00
-- url     : https://prove2.me/theorems/07f59d4c-9f6a-4bbc-bc47-43d8dfbdbc35
-- title:
--   P2 M Global Theory Field Base Change sval zero  c17798940263: P2 M Global Theory Field Base Change sval zero  c17798940263
-- statement:
--   The P2 M Global Theory Field Base Change sval zero  c17798940263 construction uses the P2 M Global Theory Field Base Change sval zero  c17798940263 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L138-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L138-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}
variable (π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
variable {π} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ

theorem P2M_GlobalTheory_FieldBaseChange_sval_zero__c17798940263 : sval (0 : SecOver π (LB.LinComb L φ ε)) r z J = 0 := by sorry

alias «GlobalTheory».«FieldBaseChange».«sval_zero'» := P2M_GlobalTheory_FieldBaseChange_sval_zero__c17798940263
