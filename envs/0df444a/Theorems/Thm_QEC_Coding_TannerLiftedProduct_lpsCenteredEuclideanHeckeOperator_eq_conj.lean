-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredEuclideanHeckeOperator_eq_conj
-- name    : QEC.Coding.TannerLiftedProduct.lpsCenteredEuclideanHeckeOperator_eq_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:55:36.754196+00:00
-- url     : https://prove2.me/theorems/a5b1afd4-ea5e-49c0-8c47-8a63f357809c
-- title:
--   Tanner Lifted Product: lps Centered Euclidean Hecke Operator eq conj
-- statement:
--   The ordinary-function and Euclidean presentations of the centered
--   Hecke operator are conjugate under the canonical `L²` identification.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L53-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L53-L87

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsCenteredEuclideanHeckeOperator_eq_conj
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredEuclideanHeckeOperator a n =
      (cayleyEuclideanLinearEquiv (G := PSL(2, ZMod a.q))).conj
        (lpsCenteredHeckeOperator a n) := by sorry
