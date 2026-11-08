-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsCenteredEuclideanHeckeOperator
-- name    : QEC.Coding.TannerLiftedProduct.trace_lpsCenteredEuclideanHeckeOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:57:50.918778+00:00
-- url     : https://prove2.me/theorems/cd12db40-990f-4ed5-872a-66bf152a0616
-- title:
--   Tanner Lifted Product: trace lps Centered Euclidean Hecke Operator
-- statement:
--   The Euclidean and ordinary-function presentations of the centered
--   Hecke operator have the same trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L174-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L174-L181

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.trace_lpsCenteredEuclideanHeckeOperator
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
        (lpsCenteredEuclideanHeckeOperator a n) =
      LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (lpsCenteredHeckeOperator a n) := by sorry
