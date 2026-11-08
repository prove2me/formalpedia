-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_degree_eq_geomSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_degree_eq_geomSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:57:30.052676+00:00
-- url     : https://prove2.me/theorems/6d45a329-b9f0-4371-9634-c4ea704ecb96
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval degree eq geom Sum
-- statement:
--   The scalar by which the `n`-th LPS Hecke operator acts on constant
--   functions is the geometric sum `1 + p + ... + p^n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L147-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L147-L151

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_degree_eq_geomSum
    (p n : ℕ) :
    (lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) =
      ∑ i ∈ Finset.range (n + 1), (p : ℂ) ^ i := by sorry
