-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrUniformizer_polynomialMapFlat
-- name    : QEC.Coding.AlgebraicGeometry.dvrUniformizer_polynomialMapFlat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:55:58.193921+00:00
-- url     : https://prove2.me/theorems/8be51ec9-e5a7-43ae-9992-21388099faea
-- title:
--   Algebraic Geometry: dvr Uniformizer polynomial Map Flat
-- statement:
--   The Algebraic Geometry construction uses the dvr Uniformizer polynomial Map Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L40-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L40-L50

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

theorem QEC.Coding.AlgebraicGeometry.dvrUniformizer_polynomialMapFlat
    (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V) (hπ : Irreducible π) :
    (Polynomial.aeval π : Polynomial k →ₐ[k] V).toRingHom.Flat := by sorry
