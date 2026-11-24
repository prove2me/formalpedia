-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HomLinear_valAt__comp_left_59bd74891c19
-- name    : P2M_GlobalTheory_HomLinear_valAt__comp_left_59bd74891c19
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:56:33.286256+00:00
-- url     : https://prove2.me/theorems/2a155459-ba7a-4eb0-ac41-c79c1ca47990
-- title:
--   P2 M Global Theory Hom Linear val At  comp left 59bd74891c19: P2 M Global Theory Hom Linear val At  comp left 59bd74891c19
-- statement:
--   The P2 M Global Theory Hom Linear val At  comp left 59bd74891c19 construction uses the P2 M Global Theory Hom Linear val At  comp left 59bd74891c19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsLinearOfIsMonHom.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsLinearOfIsMonHom.lean#L19-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HomLinear
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
omit [GrpObj A] [GrpObj A']

theorem P2M_GlobalTheory_HomLinear_valAt__comp_left_59bd74891c19 (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (f : A ⟶ A') (U : A'.left.Opens) (s : Γ(A'.left, U)) :
    valAt' (x ≫ f).left U s = valAt' x.left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) := by sorry

alias «GlobalTheory».«HomLinear».«valAt'_comp_left» := P2M_GlobalTheory_HomLinear_valAt__comp_left_59bd74891c19
