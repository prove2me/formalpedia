-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_lpsReducedWord_product_eq_or_eq_neg
-- name    : QEC.Coding.TannerLiftedProduct.exists_lpsReducedWord_product_eq_or_eq_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:53:28.998267+00:00
-- url     : https://prove2.me/theorems/e58b8d14-7a54-4e7a-ac29-64c5b96943f3
-- title:
--   Tanner Lifted Product: exists lps Reduced Word product eq or eq neg
-- statement:
--   A primitive quaternion of norm `p^n` and LPS parity is represented,
--   up to its central sign, by a reduced word of length `n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L95-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L95-L191

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.exists_lpsReducedWord_product_eq_or_eq_neg
    (a : LPSResiduePrime p) : ∀ (n : ℕ) (t : LPSQuaternion),
    t.norm = (p : ℤ) ^ n → t.HasLPSParity →
    ¬t.CoordinatesDvd (p : ℤ) →
    ∃ word : LPSReducedWord a.degreePrime.pos n,
      lpsQuaternionWordProduct word.1.1 = t ∨
        lpsQuaternionWordProduct word.1.1 = -t := by sorry
