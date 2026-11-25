-- Prove2me | Theorems.Thm_P2M_GlobalTheory_exists_appLE___eq_fe080a4f4ee7
-- name    : P2M_GlobalTheory_exists_appLE___eq_fe080a4f4ee7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:07:45.790124+00:00
-- url     : https://prove2.me/theorems/7961b772-fb60-4324-90f1-661f3edde2d5
-- title:
--   P2 M Global Theory exists app LE   eq fe080a4f4ee7: P2 M Global Theory exists app LE   eq fe080a4f4ee7
-- statement:
--   The P2 M Global Theory exists app LE   eq fe080a4f4ee7 construction uses the P2 M Global Theory exists app LE   eq fe080a4f4ee7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L102-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L102-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
set_option backward.isDefEq.respectTransparency false
include hc

theorem P2M_GlobalTheory_exists_appLE___eq_fe080a4f4ee7 {i : I} {U : (D.obj i).Opens} (hU : IsAffineOpen U)
    (s : Γ(X, π i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)),
      ((π j).appLE _ _ (cone_preimage_le D π w f U)).hom t = s := by sorry

alias «GlobalTheory».«exists_appLE_π_eq» := P2M_GlobalTheory_exists_appLE___eq_fe080a4f4ee7
