-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SymLiftOdd_comp_pow__fae19791c0f2
-- name    : P2M_GlobalTheory_SymLiftOdd_comp_pow__fae19791c0f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:52.240078+00:00
-- url     : https://prove2.me/theorems/c9d0cc5d-76b1-4469-8b69-50b53015a5b2
-- title:
--   P2 M Global Theory Sym Lift Odd comp pow  fae19791c0f2: P2 M Global Theory Sym Lift Odd comp pow  fae19791c0f2
-- statement:
--   The P2 M Global Theory Sym Lift Odd comp pow  fae19791c0f2 construction uses the P2 M Global Theory Sym Lift Odd comp pow  fae19791c0f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L111-L114

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

theorem P2M_GlobalTheory_SymLiftOdd_comp_pow__fae19791c0f2 {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) : ρ ≫ x ^ n = (ρ ≫ x) ^ n := by sorry

alias «GlobalTheory».«SymLiftOdd».«comp_pow'» := P2M_GlobalTheory_SymLiftOdd_comp_pow__fae19791c0f2
