-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_additiveSectionIso_hom_injective
-- name    : QEC.Coding.AlgebraicGeometry.additiveSectionIso_hom_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:04.617728+00:00
-- url     : https://prove2.me/theorems/168845a7-138e-4945-9be0-080e2b8c25c9
-- title:
--   Algebraic Geometry: additive Section Iso hom injective
-- statement:
--   The Algebraic Geometry construction uses the additive Section Iso hom injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L20-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L20-L24

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k (schemeRestrictionConstantMap f k c)

theorem QEC.Coding.AlgebraicGeometry.additiveSectionIso_hom_injective {A B : AddCommGrpCat.{u}} (e : A ≅ B) :
    Function.Injective e.hom := by sorry
