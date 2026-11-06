-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeRestrictionGlobal_appIso_inv_appTop
-- name    : QEC.Coding.AlgebraicGeometry.schemeRestrictionGlobal_appIso_inv_appTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:03:55.564503+00:00
-- url     : https://prove2.me/theorems/99a93da4-520d-467a-9443-f5cbebd5688f
-- title:
--   Algebraic Geometry: scheme Restriction Global app Iso inv app Top
-- statement:
--   The Algebraic Geometry construction uses the scheme Restriction Global app Iso inv app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L46-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L46-L52

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

theorem QEC.Coding.AlgebraicGeometry.schemeRestrictionGlobal_appIso_inv_appTop (a : Γ(X, ⊤)) :
    (f.appIso ⊤).inv (f.appTop a) =
      X.presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op a := by sorry
