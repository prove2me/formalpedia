-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterLocalFibre_isField
-- name    : QEC.Coding.AlgebraicGeometry.dvrParameterLocalFibre_isField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:45.362201+00:00
-- url     : https://prove2.me/theorems/bff77fb1-0eb9-4bfd-870e-1f6a02f442d8
-- title:
--   Algebraic Geometry: dvr Parameter Local Fibre is Field
-- statement:
--   The Algebraic Geometry construction uses the dvr Parameter Local Fibre is Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L179-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L179-L196

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime

theorem QEC.Coding.AlgebraicGeometry.dvrParameterLocalFibre_isField
    [IsDiscreteValuationRing V] (hπ : Irreducible π) :
    let R := Localization.AtPrime (dvrParameterPrime k V π)
    letI : Algebra R V :=
      (dvrParameterLocalMap k V π).toRingHom.toAlgebra
    IsField (IsLocalRing.ResidueField R ⊗[R] V) := by sorry
