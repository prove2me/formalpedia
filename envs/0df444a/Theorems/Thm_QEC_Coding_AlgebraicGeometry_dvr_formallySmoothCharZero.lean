-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvr_formallySmoothCharZero
-- name    : QEC.Coding.AlgebraicGeometry.dvr_formallySmoothCharZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:48.923677+00:00
-- url     : https://prove2.me/theorems/998383d3-e832-4231-a3bc-4d7dac8d597e
-- title:
--   Algebraic Geometry: dvr formally Smooth Char Zero
-- statement:
--   The Algebraic Geometry construction uses the dvr formally Smooth Char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L200-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L200-L237

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

theorem QEC.Coding.AlgebraicGeometry.dvr_formallySmoothCharZero
    [CharZero k] [IsDiscreteValuationRing V] [Algebra.EssFiniteType k V] :
    Algebra.FormallySmooth k V := by sorry
