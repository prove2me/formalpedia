-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_action_eq_centered_add_constant
-- name    : QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_action_eq_centered_add_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:55:48.974083+00:00
-- url     : https://prove2.me/theorems/9da0ad75-b01e-43c2-aa54-447d49ff2980
-- title:
--   Tanner Lifted Product: lps Finite Hecke Element action eq centered add constant
-- statement:
--   Polynomial functional calculus splits into the centered LPS operator
--   plus its one-dimensional constant-mode contribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L91-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L91-L129

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_action_eq_centered_add_constant
    (a : LPSResiduePrime p) (n : ℕ) :
    cayleyRightRegularRepresentation.asAlgebraHom
        (lpsFiniteHeckeElement a n) =
      lpsCenteredHeckeOperator a n +
        ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) •
            cayleyConstantProjection := by sorry
