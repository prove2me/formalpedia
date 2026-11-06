-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIso_smul
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:03:53.386593+00:00
-- url     : https://prove2.me/theorems/1ba5ff84-0e7a-4376-a039-9eedf55c3452
-- title:
--   Algebraic Geometry: scheme Differential Restriction Image Section Iso smul
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Restriction Image Section Iso smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L40-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L40-L44

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

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_smul (U : Y.Opens)
    (a : Γ(Y, U)) (s : Γ(OmegaY, U)) :
    (schemeDifferentialRestrictionImageSectionIso f k c U).hom (a • s) =
      (f.appIso U).inv a • (schemeDifferentialRestrictionImageSectionIso f k c U).hom s := by sorry
