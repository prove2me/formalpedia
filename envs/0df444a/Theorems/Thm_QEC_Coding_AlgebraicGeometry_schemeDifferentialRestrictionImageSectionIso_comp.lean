-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIso_comp
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:38.789359+00:00
-- url     : https://prove2.me/theorems/68711d0a-d2f3-48f8-a57e-c31913d834d8
-- title:
--   Algebraic Geometry: scheme Differential Restriction Image Section Iso comp
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Restriction Image Section Iso comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L114-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L114-L123

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "cY" => schemeRestrictionConstantMap f k c
local notation "cZ" => schemeRestrictionConstantMap g k cY
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k cY
local notation "OmegaZ" => schemeDifferentialSheaf Z k cZ

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_comp (U : Z.Opens) (s : Γ(OmegaZ, U)) :
    (schemeDifferentialRestrictionImageSectionIsoTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c) U).hom s =
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f U)).op
      ((schemeDifferentialRestrictionImageSectionIso f k c (g ''ᵁ U)).hom
        ((schemeDifferentialRestrictionImageSectionIso g k cY U).hom s)) := by sorry
