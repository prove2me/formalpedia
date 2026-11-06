-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionComparison_comp
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionComparison_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:42.864759+00:00
-- url     : https://prove2.me/theorems/fe37ad40-bc1e-4ae3-a52b-a93642fbb74e
-- title:
--   Algebraic Geometry: scheme Differential Restriction Comparison comp
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Restriction Comparison comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L56-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L56-L96

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

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionComparison_comp :
    schemeDifferentialRestrictionComparisonTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c) =
    schemeDifferentialRestrictionComparisonComposite f g k c := by sorry
