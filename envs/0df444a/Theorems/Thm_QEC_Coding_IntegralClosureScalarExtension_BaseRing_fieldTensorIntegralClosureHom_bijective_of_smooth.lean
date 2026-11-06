-- Prove2me | Theorems.Thm_QEC_Coding_IntegralClosureScalarExtension_BaseRing_fieldTensorIntegralClosureHom_bijective_of_smooth
-- name    : QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_bijective_of_smooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:47.85842+00:00
-- url     : https://prove2.me/theorems/1343bfd9-1615-4a3b-9096-0882ad4912bf
-- title:
--   Base Ring: field Tensor Integral Closure Hom bijective of smooth
-- statement:
--   The Base Ring construction uses the field Tensor Integral Closure Hom bijective of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureScalarExtension.lean#L492-L504
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureScalarExtension.lean#L492-L504

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

theorem QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_bijective_of_smooth [Algebra.Smooth K F]
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    Function.Bijective (fieldTensorIntegralClosureHom (K := K) (F := F) (B0 := B0) R) := by sorry
