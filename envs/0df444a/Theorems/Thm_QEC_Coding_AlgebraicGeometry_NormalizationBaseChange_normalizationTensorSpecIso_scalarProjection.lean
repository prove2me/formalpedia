-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationTensorSpecIso_scalarProjection
-- name    : QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_scalarProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:12:58.259745+00:00
-- url     : https://prove2.me/theorems/a8a6395d-130d-4aa2-974f-2efbc1b96955
-- title:
--   Normalization Base Change: normalization Tensor Spec Iso scalar Projection
-- statement:
--   The Normalization Base Change construction uses the normalization Tensor Spec Iso scalar Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L72-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L72-L82

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]

theorem QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_scalarProjection (e : S ⊗[R] A ≃ₐ[S] B) :
    (normalizationTensorSpecIso e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S B)) := by sorry
