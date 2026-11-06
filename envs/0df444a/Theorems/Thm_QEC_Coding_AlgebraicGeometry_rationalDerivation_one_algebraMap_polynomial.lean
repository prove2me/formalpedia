-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_rationalDerivation_one_algebraMap_polynomial
-- name    : QEC.Coding.AlgebraicGeometry.rationalDerivation_one_algebraMap_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:04.094941+00:00
-- url     : https://prove2.me/theorems/113be528-5a7d-40e7-862f-f06f5acd8f7b
-- title:
--   Algebraic Geometry: rational Derivation one algebra Map polynomial
-- statement:
--   The rational derivation with value one at `X` restricts to formal
--   polynomial differentiation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialMatrixDerivation.lean#L41-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialMatrixDerivation.lean#L41-L58

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.rationalDerivation_one_algebraMap_polynomial (p : k[X]) :
    RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1
        (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (RatFunc k) p.derivative := by sorry
