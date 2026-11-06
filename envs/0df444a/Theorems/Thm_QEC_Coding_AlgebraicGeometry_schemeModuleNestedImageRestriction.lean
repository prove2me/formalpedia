-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModuleNestedImageRestriction
-- name    : QEC.Coding.AlgebraicGeometry.schemeModuleNestedImageRestriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:05:23.992606+00:00
-- url     : https://prove2.me/theorems/79c224a7-fda1-476d-8699-209d7926fb6d
-- title:
--   Algebraic Geometry: scheme Module Nested Image Restriction
-- statement:
--   The Algebraic Geometry construction uses the scheme Module Nested Image Restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L227-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L227-L232

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]

theorem QEC.Coding.AlgebraicGeometry.schemeModuleNestedImageRestriction (M : X.Modules) (s : Γ(M, f ''ᵁ ⊤)) :
    M.presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op
      (M.presheaf.map (f.opensFunctor.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤)).op s) =
    M.presheaf.map (homOfLE (schemeNestedImage_le f g)).op s := by sorry
