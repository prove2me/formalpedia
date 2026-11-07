-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionGL_eq_away
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionGL_eq_away
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:37:58.834757+00:00
-- url     : https://prove2.me/theorems/ca67e5cf-85c3-41ef-94c9-c07bfb2fd8b5
-- title:
--   Tanner Lifted Product: lps Quaternion GL eq away
-- statement:
--   The original norm-`p` general-linear reduction is exactly the
--   restriction of the multiplicative norm-away construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionReduction.lean#L85-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionReduction.lean#L85-L91

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionGL_eq_away
    (a : LPSResiduePrime p) (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionGL a t ht =
      lpsQuaternionAwayGL a.q (lpsQuaternionAwayElement a t ht) := by sorry
