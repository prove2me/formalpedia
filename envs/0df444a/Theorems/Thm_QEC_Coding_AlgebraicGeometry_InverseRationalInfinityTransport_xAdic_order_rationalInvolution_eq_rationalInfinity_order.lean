-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_xAdic_order_rationalInvolution_eq_rationalInfinity_order
-- name    : QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.xAdic_order_rationalInvolution_eq_rationalInfinity_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:57.758579+00:00
-- url     : https://prove2.me/theorems/e2599670-744b-4d19-a5a4-0655a9277b10
-- title:
--   Inverse Rational Infinity Transport: x Adic order rational Involution eq rational Infinity order
-- statement:
--   The concrete `(X)`-adic order after inversion is the original
--   rational-infinity order.  This is the exact reusable base-place transport
--   needed by the inverse-fibre normalized-factor calculation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/RationalInfinityTransport.lean#L234-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/RationalInfinityTransport.lean#L234-L245

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Norm.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped LaurentPolynomial Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]

theorem QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.xAdic_order_rationalInvolution_eq_rationalInfinity_order
    (h : RatFunc k) :
    GlobalPlace.order (xAdicPlace k)
      (InverseAffinePlace.rationalInvolution k h) =
      GlobalPlace.order (GlobalPlace.rationalInfinity k) h := by sorry
