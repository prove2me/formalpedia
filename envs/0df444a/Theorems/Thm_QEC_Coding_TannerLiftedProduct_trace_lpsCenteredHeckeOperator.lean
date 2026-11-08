-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsCenteredHeckeOperator
-- name    : QEC.Coding.TannerLiftedProduct.trace_lpsCenteredHeckeOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:57:38.611232+00:00
-- url     : https://prove2.me/theorems/1d03a5f1-9b10-44a7-bda1-ed2fef95c6f9
-- title:
--   Tanner Lifted Product: trace lps Centered Hecke Operator
-- statement:
--   The trace of the centered Hecke operator is the full finite trace with
--   the single trivial-representation eigenvalue removed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L155-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L155-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.trace_lpsCenteredHeckeOperator
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (lpsCenteredHeckeOperator a n) =
      LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
          (cayleyRightRegularRepresentation.asAlgebraHom
            (lpsFiniteHeckeElement a n)) -
        ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by sorry
