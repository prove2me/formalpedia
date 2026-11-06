-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionIso_derivation
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionIso_derivation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:02:57.975984+00:00
-- url     : https://prove2.me/theorems/6cb77c06-0f14-4af4-9aa5-c6d000e552b6
-- title:
--   Algebraic Geometry: scheme Differential Restriction Iso derivation
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Restriction Iso derivation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestriction.lean#L296-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestriction.lean#L296-L303

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerRingIso
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionIso_derivation :
    (schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).postcomp
      ((Scheme.Modules.toPresheafOfModules Y).map (schemeDifferentialRestrictionIso f k c).hom) =
    schemeRestrictedDifferentialSheafDerivation f k c := by sorry
