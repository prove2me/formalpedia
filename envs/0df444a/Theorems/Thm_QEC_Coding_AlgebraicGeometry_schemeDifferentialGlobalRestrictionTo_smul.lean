-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialGlobalRestrictionTo_smul
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestrictionTo_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:03.780195+00:00
-- url     : https://prove2.me/theorems/7dd6a68b-8349-4079-b066-b1acf62af6ab
-- title:
--   Algebraic Geometry: scheme Differential Global Restriction To smul
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Global Restriction To smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L131-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L131-L135

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (h : schemeRestrictionConstantMap f k c = d)
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k d

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestrictionTo_smul (a : Γ(X, ⊤)) (s : Γ(OmegaX, ⊤)) :
    schemeDifferentialGlobalRestrictionTo f k c d h (a • s) =
      f.appTop a • schemeDifferentialGlobalRestrictionTo f k c d h s := by sorry
