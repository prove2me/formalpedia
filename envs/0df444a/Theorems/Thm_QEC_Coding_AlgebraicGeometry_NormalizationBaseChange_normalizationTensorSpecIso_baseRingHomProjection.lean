-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationTensorSpecIso_baseRingHomProjection
-- name    : QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_baseRingHomProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:13:01.916203+00:00
-- url     : https://prove2.me/theorems/b7c6fbba-ae17-412d-8155-94e1e0584acc
-- title:
--   Normalization Base Change: normalization Tensor Spec Iso base Ring Hom Projection
-- statement:
--   The Normalization Base Change construction uses the normalization Tensor Spec Iso base Ring Hom Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L94-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L94-L102

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]

theorem QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_baseRingHomProjection (e : S ⊗[R] A ≃ₐ[S] B) :
    (normalizationTensorSpecIso e).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (normalizationBaseRingHom e.toRingHom)) := by sorry
