-- Prove2me | Theorems.Thm_P2M_GlobalTheory_OriginValue_eq_of_valAt__eq_of_isIso_0aa59719e453
-- name    : P2M_GlobalTheory_OriginValue_eq_of_valAt__eq_of_isIso_0aa59719e453
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:32.552509+00:00
-- url     : https://prove2.me/theorems/30cb6b93-ba5c-4454-a71d-cb12550cd08a
-- title:
--   P2 M Global Theory Origin Value eq of val At  eq of is Iso 0aa59719e453: P2 M Global Theory Origin Value eq of val At  eq of is Iso 0aa59719e453
-- statement:
--   The P2 M Global Theory Origin Value eq of val At  eq of is Iso 0aa59719e453 construction uses the P2 M Global Theory Origin Value eq of val At  eq of is Iso 0aa59719e453 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenIsValueAtOrigin.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenIsValueAtOrigin.lean#L16-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenIsValueAtOrigin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.OriginValue

theorem P2M_GlobalTheory_OriginValue_eq_of_valAt__eq_of_isIso_0aa59719e453 {X : Scheme.{0}} (x : Sp ℂ ⟶ X) [IsIso x] (W : X.Opens) (f g : Γ(X, W))
    (h : ⊤ ≤ x ⁻¹ᵁ W → valAt' x W f = valAt' x W g) : f = g := by sorry

alias «GlobalTheory».«OriginValue».«eq_of_valAt'_eq_of_isIso» := P2M_GlobalTheory_OriginValue_eq_of_valAt__eq_of_isIso_0aa59719e453
