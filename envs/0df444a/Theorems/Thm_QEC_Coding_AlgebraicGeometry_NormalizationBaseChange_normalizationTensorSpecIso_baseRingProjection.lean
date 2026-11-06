-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationTensorSpecIso_baseRingProjection
-- name    : QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_baseRingProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:30.440195+00:00
-- url     : https://prove2.me/theorems/b76cb209-a5dc-45a5-8a66-dfaad3e76d92
-- title:
--   Normalization Base Change: normalization Tensor Spec Iso base Ring Projection
-- statement:
--   The Normalization Base Change construction uses the normalization Tensor Spec Iso base Ring Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L63-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L63-L70

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]

theorem QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_baseRingProjection (e : S ⊗[R] A ≃ₐ[S] B) :
    (normalizationTensorSpecIso e).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)) := by sorry
