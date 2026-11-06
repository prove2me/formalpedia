-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIso_D
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:21.783094+00:00
-- url     : https://prove2.me/theorems/b3748c62-aee9-4065-8c20-b457fb0b4ff6
-- title:
--   Algebraic Geometry: scheme Differential Restriction Image Section Iso D
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Restriction Image Section Iso D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L31-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L31-L38

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

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_D (U : Y.Opens) (a : Γ(Y, U)) :
    (schemeDifferentialRestrictionImageSectionIso f k c U).hom
      ((schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).d
        (X := op U) a) =
    (schemeDifferentialSheafDerivation X k c).d (X := op (f ''ᵁ U))
      ((f.appIso U).inv a) := by sorry
