-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationConstantRingHom_apply
-- name    : QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationConstantRingHom_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:12:51.432769+00:00
-- url     : https://prove2.me/theorems/ddc40816-590f-49e5-9e0c-78938714b8ed
-- title:
--   Normalization Base Change: normalization Constant Ring Hom apply
-- statement:
--   The Normalization Base Change construction uses the normalization Constant Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L45-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L45-L46

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
open scoped TensorProduct
variable {R₀ S₀ A₀ D₀ : Type} [CommRing R₀] [CommRing S₀] [CommRing A₀] [CommRing D₀]
  [Algebra R₀ S₀] [Algebra R₀ A₀]

theorem QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationConstantRingHom_apply (e : S₀ ⊗[R₀] A₀ →+* D₀) (c : S₀) :
    normalizationConstantRingHom e c = e (c ⊗ₜ[R₀] (1 : A₀)) := by sorry
