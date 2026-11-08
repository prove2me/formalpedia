-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_trace_lpsCenteredEuclideanHeckeOperator_eq_theta_sub_trivial
-- name    : QEC.Coding.TannerLiftedProduct.two_mul_trace_lpsCenteredEuclideanHeckeOperator_eq_theta_sub_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:57:05.946918+00:00
-- url     : https://prove2.me/theorems/cba9cda0-43e8-4b15-81cf-9d1390ed914e
-- title:
--   Tanner Lifted Product: two mul trace lps Centered Euclidean Hecke Operator eq theta sub trivial
-- statement:
--   Euclidean-space form of the exact centered trace formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L214-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L214-L223

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.two_mul_trace_lpsCenteredEuclideanHeckeOperator_eq_theta_sub_trivial
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * LinearMap.trace ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
          (lpsCenteredEuclideanHeckeOperator a n) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
          ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) -
        2 * ((∑ i ∈ Finset.range (n + 1), (p : ℂ) ^ i) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by sorry
