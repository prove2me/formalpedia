-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_dedekindFiniteType_smoothCharZero
-- name    : QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:56:43.093783+00:00
-- url     : https://prove2.me/theorems/b56a2f84-2eee-40c8-9789-bef370662662
-- title:
--   Algebraic Geometry: dedekind Finite Type smooth Char Zero
-- statement:
--   The Algebraic Geometry construction uses the dedekind Finite Type smooth Char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L246-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L246-L265

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

theorem QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero
    (k A : Type*) [Field k] [CharZero k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    Algebra.Smooth k A := by sorry
