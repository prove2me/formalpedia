-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialGlobalRestriction_D
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestriction_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:13.272487+00:00
-- url     : https://prove2.me/theorems/241af30c-47fb-4bfc-9056-2fe0e5b61ae6
-- title:
--   Algebraic Geometry: scheme Differential Global Restriction D
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Global Restriction D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L79-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean#L79-L105

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

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestriction_D (a : Γ(X, ⊤)) :
    schemeDifferentialGlobalRestriction f k c
      ((schemeDifferentialSheafDerivation X k c).d (X := op ⊤) a) =
    (schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).d
      (X := op ⊤) (f.appTop a) := by sorry
