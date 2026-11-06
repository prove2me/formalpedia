-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_transported_norm_xAdic_to_original_infinity
-- name    : QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.transported_norm_xAdic_to_original_infinity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:44:28.449673+00:00
-- url     : https://prove2.me/theorems/9da1aaa2-f30d-4c75-b6f1-1184decaa7b2
-- title:
--   Inverse Rational Infinity Transport: transported norm x Adic to original infinity
-- statement:
--   The exact bridge consumed by the final inverse-fibre local calculation.
--   After the local normalized-factor proof identifies the finite fibre degree
--   with the X-adic order of the transported norm, this theorem changes only the
--   base coordinate and yields the original rational-infinity order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/RationalInfinityTransport.lean#L280-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/RationalInfinityTransport.lean#L280-L290

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

theorem QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.transported_norm_xAdic_to_original_infinity (f : F) :
    letI : Algebra k⟮X⟯ F :=
      InverseAffinePlace.transportedRationalAlgebra k F
    GlobalPlace.order (xAdicPlace k) (Algebra.norm k⟮X⟯ f) =
      GlobalPlace.order (GlobalPlace.rationalInfinity k)
        (@Algebra.norm k⟮X⟯ F _ _ oldRationalAlgebra f) := by sorry
