-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SymLiftOdd_comp_inv__c2958fec9ffd
-- name    : P2M_GlobalTheory_SymLiftOdd_comp_inv__c2958fec9ffd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:55.196117+00:00
-- url     : https://prove2.me/theorems/d06a9415-7b1b-49d6-8164-859f1d6ed1e4
-- title:
--   P2 M Global Theory Sym Lift Odd comp inv  c2958fec9ffd: P2 M Global Theory Sym Lift Odd comp inv  c2958fec9ffd
-- statement:
--   The P2 M Global Theory Sym Lift Odd comp inv  c2958fec9ffd construction uses the P2 M Global Theory Sym Lift Odd comp inv  c2958fec9ffd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L116-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SymLiftOdd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem P2M_GlobalTheory_SymLiftOdd_comp_inv__c2958fec9ffd {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ A) : ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ := by sorry

alias «GlobalTheory».«SymLiftOdd».«comp_inv'» := P2M_GlobalTheory_SymLiftOdd_comp_inv__c2958fec9ffd
