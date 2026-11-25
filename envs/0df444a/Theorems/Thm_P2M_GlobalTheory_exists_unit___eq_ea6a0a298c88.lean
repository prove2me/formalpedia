-- Prove2me | Theorems.Thm_P2M_GlobalTheory_exists_unit___eq_ea6a0a298c88
-- name    : P2M_GlobalTheory_exists_unit___eq_ea6a0a298c88
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:06:54.013441+00:00
-- url     : https://prove2.me/theorems/b0293e6e-96ea-448d-be52-e5405eadb959
-- title:
--   P2 M Global Theory exists unit   eq ea6a0a298c88: P2 M Global Theory exists unit   eq ea6a0a298c88
-- statement:
--   The P2 M Global Theory exists unit   eq ea6a0a298c88 construction uses the P2 M Global Theory exists unit   eq ea6a0a298c88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L121-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L121-L147

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
include hc

theorem P2M_GlobalTheory_exists_unit___eq_ea6a0a298c88 {i : I} {U : (D.obj i).Opens} (hU : IsAffineOpen U)
    (s : Γ(X, π i ⁻¹ᵁ U)ˣ) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)ˣ), ∀ y : X, y ∈ π i ⁻¹ᵁ U →
      gm (π j) y (D.map f ⁻¹ᵁ U) t = gm (𝟙 X) y (π i ⁻¹ᵁ U) s := by sorry

alias «GlobalTheory».«exists_unit_π_eq» := P2M_GlobalTheory_exists_unit___eq_ea6a0a298c88
