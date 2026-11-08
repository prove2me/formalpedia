-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionAwayPGL_eq_one_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionAwayPGL_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:48:21.991072+00:00
-- url     : https://prove2.me/theorems/547db4d9-1ba6-495a-928b-314cea8c315a
-- title:
--   Tanner Lifted Product: lps Quaternion Away PGL eq one iff
-- statement:
--   Projective quaternion reduction is the identity exactly when the three
--   imaginary coordinates vanish modulo the residue prime.  This is the local
--   algebraic core of the identity-coefficient count in the LPS trace formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionReduction.lean#L105-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionReduction.lean#L105-L185

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionAwayPGL_eq_one_iff
    (a : LPSResiduePrime p)
    (t : lpsQuaternionAwaySubmonoid a.q) :
    lpsQuaternionAwayPGL a.q t = 1 ↔
      (a.q : ℤ) ∣ t.1.b ∧
        (a.q : ℤ) ∣ t.1.c ∧
          (a.q : ℤ) ∣ t.1.d := by sorry
