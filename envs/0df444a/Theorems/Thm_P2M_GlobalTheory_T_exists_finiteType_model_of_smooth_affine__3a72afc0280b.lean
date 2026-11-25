-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_finiteType_model_of_smooth_affine__3a72afc0280b
-- name    : P2M_GlobalTheory_T_exists_finiteType_model_of_smooth_affine__3a72afc0280b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:02:28.956259+00:00
-- url     : https://prove2.me/theorems/12ee81a7-8e01-4516-8ed9-557394bb2e75
-- title:
--   P2 M Global Theory T exists finite Type model of smooth affine  3a72afc0280b: P2 M Global Theory T exists finite Type model of smooth affine  3a72afc0280b
-- statement:
--   The P2 M Global Theory T exists finite Type model of smooth affine  3a72afc0280b construction uses the P2 M Global Theory T exists finite Type model of smooth affine  3a72afc0280b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteTypeModelOfSmoothAffineStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteTypeModelOfSmoothAffineStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteTypeModelOfSmoothAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteTypeModelOfSmoothAffineStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem P2M_GlobalTheory_T_exists_finiteType_model_of_smooth_affine__3a72afc0280b : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (p : X ⟶ Sp V), IsAffine X → Smooth p → ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth p₀ ∧ IsAffine X₀ ∧ IsPullback φ p p₀ (spMap f) := by sorry

alias «GlobalTheory».«T».«exists_finiteType_model_of_smooth_affine'» := P2M_GlobalTheory_T_exists_finiteType_model_of_smooth_affine__3a72afc0280b
