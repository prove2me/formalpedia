-- Prove2me | Theorems.Thm_QEC_Coding_IntegralClosureScalarExtension_BaseRing_fieldChartTensorCancelIntegralClosure_naturality
-- name    : QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldChartTensorCancelIntegralClosure_naturality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:47:18.41486+00:00
-- url     : https://prove2.me/theorems/ab05318b-9aa7-41de-a5e8-407ec0adfe1d
-- title:
--   Base Ring: field Chart Tensor Cancel Integral Closure naturality
-- statement:
--   The Base Ring construction uses the field Chart Tensor Cancel Integral Closure naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureScalarExtension.lean#L445-L461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureScalarExtension.lean#L445-L461

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

theorem QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldChartTensorCancelIntegralClosure_naturality (E : Type*) [CommRing E] [Algebra K E]
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0]
    (z : (E ⊗[K] R) ⊗[R] integralClosure R B0) :
    fieldChartTensorCancelEquiv (K := K) E R
      (Algebra.TensorProduct.map (AlgHom.id R (E ⊗[K] R)) (integralClosure R B0).val z) =
    Algebra.TensorProduct.map (AlgHom.id K E)
      ((integralClosure R B0).val.restrictScalars K)
      (fieldChartTensorCancelEquiv (K := K) E R z) := by sorry
