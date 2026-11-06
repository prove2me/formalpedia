-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIso_globalRestriction
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_globalRestriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:40.794665+00:00
-- url     : https://prove2.me/theorems/75a88423-346f-42db-ab2a-2818673613a8
-- title:
--   Algebraic Geometry: scheme Differential Restriction Image Section Iso global Restriction
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Restriction Image Section Iso global Restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L135-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L135-L155

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

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_globalRestriction
    (s : Γ(OmegaY, ⊤)) :
    (schemeDifferentialRestrictionImageSectionIsoTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c) ⊤).hom
        (schemeDifferentialGlobalRestriction g k cY s) =
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op
      ((OmegaX).presheaf.map
        (f.opensFunctor.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤)).op
          ((schemeDifferentialRestrictionImageSectionIso f k c ⊤).hom s)) := by sorry
