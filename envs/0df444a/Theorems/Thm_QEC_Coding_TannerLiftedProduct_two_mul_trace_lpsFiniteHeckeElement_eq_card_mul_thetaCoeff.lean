-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_trace_lpsFiniteHeckeElement_eq_card_mul_thetaCoeff
-- name    : QEC.Coding.TannerLiftedProduct.two_mul_trace_lpsFiniteHeckeElement_eq_card_mul_thetaCoeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:56:36.039121+00:00
-- url     : https://prove2.me/theorems/6cfea294-d61f-40bf-9a34-48bba5c3c27f
-- title:
--   Tanner Lifted Product: two mul trace lps Finite Hecke Element eq card mul theta Coeff
-- statement:
--   Exact trace formula: twice the trace of the `n`-th finite LPS Hecke
--   operator is the group order times the corresponding trace-theta coefficient.
--   No asymptotic or automorphic input remains in this identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L134-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean#L134-L143

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.two_mul_trace_lpsFiniteHeckeElement_eq_card_mul_thetaCoeff
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
          (cayleyRightRegularRepresentation.asAlgebraHom
            (lpsFiniteHeckeElement a n)) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
        ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) := by sorry
