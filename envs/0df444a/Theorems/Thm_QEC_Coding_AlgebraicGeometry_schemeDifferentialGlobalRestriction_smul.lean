-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialGlobalRestriction_smul
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestriction_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:39.705957+00:00
-- url     : https://prove2.me/theorems/699e5f27-9639-4cc7-8069-c1630b563834
-- title:
--   Algebraic Geometry: scheme Differential Global Restriction smul
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Global Restriction smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L58-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L58-L77

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

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestriction_smul (a : Γ(X, ⊤)) (s : Γ(OmegaX, ⊤)) :
    schemeDifferentialGlobalRestriction f k c (a • s) =
      f.appTop a • schemeDifferentialGlobalRestriction f k c s := by sorry
