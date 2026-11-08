-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_trace_lpsCenteredHeckeOperator_eq_theta_sub_trivial
-- name    : QEC.Coding.TannerLiftedProduct.two_mul_trace_lpsCenteredHeckeOperator_eq_theta_sub_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:57:41.684037+00:00
-- url     : https://prove2.me/theorems/6fd67961-41b1-4fd3-b622-3ce3d5cae183
-- title:
--   Tanner Lifted Product: two mul trace lps Centered Hecke Operator eq theta sub trivial
-- statement:
--   Exact centered trace formula.  The only term not supplied by
--   the theta coefficient is the explicitly removed geometric-sum contribution
--   of the constant representation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L186-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L186-L211

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.two_mul_trace_lpsCenteredHeckeOperator_eq_theta_sub_trivial
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
          (lpsCenteredHeckeOperator a n) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
          ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) -
        2 * ((∑ i ∈ Finset.range (n + 1), (p : ℂ) ^ i) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by sorry
