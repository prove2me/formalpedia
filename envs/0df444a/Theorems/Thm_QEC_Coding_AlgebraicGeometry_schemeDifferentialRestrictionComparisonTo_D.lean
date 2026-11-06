-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionComparisonTo_D
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionComparisonTo_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:05:07.868891+00:00
-- url     : https://prove2.me/theorems/9339058a-4871-44da-bc53-6b9bcfca51ad
-- title:
--   Algebraic Geometry: scheme Differential Restriction Comparison To D
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Restriction Comparison To D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L33-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean#L33-L43

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

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionComparisonTo_D
    {W V : Scheme.{u}} (i : W ⟶ V) [IsOpenImmersion i]
    (b : CommRingCat.{u}) (a : b ⟶ Γ(V, ⊤)) (d : b ⟶ Γ(W, ⊤))
    (h : schemeRestrictionConstantMap i b a = d) (U : W.Opens) (x : Γ(W, U)) :
    (schemeDifferentialRestrictionComparisonTo i b a d h).app U
      ((schemeDifferentialSheafDerivation W b d).d (X := op U) x) =
    (schemeDifferentialSheafDerivation V b a).d (X := op (i ''ᵁ U))
      ((i.appIso U).inv x) := by sorry
