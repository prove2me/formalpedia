-- Prove2me | Theorems.Thm_QEC_Coding_IntegralClosureScalarExtension_BaseRing_fieldTensorIntegralClosureHom_val
-- name    : QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:59.972313+00:00
-- url     : https://prove2.me/theorems/6901b113-ddb0-40b0-98ee-5773e6a4463d
-- title:
--   Base Ring: field Tensor Integral Closure Hom val
-- statement:
--   The Base Ring construction uses the field Tensor Integral Closure Hom val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureScalarExtension.lean#L475-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureScalarExtension.lean#L475-L490

import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureScalarExtension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.IntegralClosureScalarExtension
open scoped TensorProduct
noncomputable section
variable {k L B : Type*} [Field k] [Field L] [Algebra k L]
  [CommRing B] [Algebra k B] [Algebra.IsAlgebraic k L]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] QEC.Coding.IntegralClosureScalarExtension.fieldNativeBaseAlgebra
attribute [local instance] QEC.Coding.IntegralClosureScalarExtension.fieldRightBaseModule
open QEC.Coding.IntegralClosureScalarExtension.BaseRing
variable {K F B0 : Type*} [CommRing K] [CommRing F] [Algebra K F]
  [CommRing B0] [Algebra K B0]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldRightBaseModule

theorem QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_val
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    let : Algebra (F ⊗[K] R) (F ⊗[K] B0) :=
      (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K R B0)).toAlgebra
    ∀ z : F ⊗[K] integralClosure R B0,
      (fieldTensorIntegralClosureHom (K := K) (F := F) R z).val =
        Algebra.TensorProduct.map (AlgHom.id K F)
          ((integralClosure R B0).val.restrictScalars K) z := by sorry
