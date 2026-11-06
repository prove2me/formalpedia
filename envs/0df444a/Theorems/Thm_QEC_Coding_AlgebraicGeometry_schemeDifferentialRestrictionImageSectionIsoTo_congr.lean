-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIsoTo_congr
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIsoTo_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:39.699782+00:00
-- url     : https://prove2.me/theorems/726203f1-e616-4539-9f8f-44e9095a54e7
-- title:
--   Algebraic Geometry: scheme Differential Restriction Image Section Iso To congr
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Restriction Image Section Iso To congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L200-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L200-L211

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (i j : Y ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (hi : schemeRestrictionConstantMap i k c = d)
variable (hj : schemeRestrictionConstantMap j k c = d)
local notation "OmegaX" => schemeDifferentialSheaf X k c

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIsoTo_congr
    (h : i = j) (U : Y.Opens) (s : Γ(schemeDifferentialSheaf Y k d, U)) :
    (schemeDifferentialRestrictionImageSectionIsoTo i k c d hi U).hom s =
    (OmegaX).presheaf.map (eqToHom (schemeOpenImmersionImage_congr i j h U)).op
      ((schemeDifferentialRestrictionImageSectionIsoTo j k c d hj U).hom s) := by sorry
