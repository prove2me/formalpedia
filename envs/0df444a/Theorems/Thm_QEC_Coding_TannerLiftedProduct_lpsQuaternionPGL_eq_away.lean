-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPGL_eq_away
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionPGL_eq_away
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:47:53.330273+00:00
-- url     : https://prove2.me/theorems/bc06436a-638a-4362-a7a2-e70c3712bcc1
-- title:
--   Tanner Lifted Product: lps Quaternion PGL eq away
-- statement:
--   The original projective LPS generator is the norm-`p` slice of the
--   multiplicative projective reduction homomorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionReduction.lean#L95-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionReduction.lean#L95-L100

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionPGL_eq_away
    (a : LPSResiduePrime p) (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPGL a t ht =
      lpsQuaternionAwayPGL a.q (lpsQuaternionAwayElement a t ht) := by sorry
