-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionAwayPGL_wordProduct_eq_one_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionAwayPGL_wordProduct_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:47:05.123807+00:00
-- url     : https://prove2.me/theorems/2ffd712a-387f-4865-9eec-341b5754419c
-- title:
--   Tanner Lifted Product: lps Quaternion Away PGL word Product eq one iff
-- statement:
--   On genuine LPS generator words, reduction to the projective identity is
--   equivalent to the `2q` divisibility condition of the trace theta series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L172-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L172-L189

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionAwayPGL_wordProduct_eq_one_iff
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    lpsQuaternionAwayPGL a.q (lpsQuaternionAwayWordProduct a word) = 1 ↔
      ((2 * a.q : ℕ) : ℤ) ∣ (lpsQuaternionWordProduct word).b ∧
        ((2 * a.q : ℕ) : ℤ) ∣ (lpsQuaternionWordProduct word).c ∧
          ((2 * a.q : ℕ) : ℤ) ∣ (lpsQuaternionWordProduct word).d := by sorry
