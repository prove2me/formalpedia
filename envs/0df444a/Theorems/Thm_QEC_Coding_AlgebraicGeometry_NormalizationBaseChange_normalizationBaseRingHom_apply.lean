-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationBaseRingHom_apply
-- name    : QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationBaseRingHom_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:12:50.784793+00:00
-- url     : https://prove2.me/theorems/0cd496ee-11b8-4811-b0c9-e4aecfbeeaf1
-- title:
--   Normalization Base Change: normalization Base Ring Hom apply
-- statement:
--   The Normalization Base Change construction uses the normalization Base Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L31-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L31-L32

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
open scoped TensorProduct
variable {R₀ S₀ A₀ D₀ : Type} [CommRing R₀] [CommRing S₀] [CommRing A₀] [CommRing D₀]
  [Algebra R₀ S₀] [Algebra R₀ A₀]

theorem QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationBaseRingHom_apply (e : S₀ ⊗[R₀] A₀ →+* D₀) (x : A₀) :
    normalizationBaseRingHom e x = e ((1 : S₀) ⊗ₜ[R₀] x) := by sorry
