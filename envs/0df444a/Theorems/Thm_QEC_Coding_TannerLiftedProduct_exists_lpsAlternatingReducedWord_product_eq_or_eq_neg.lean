-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_lpsAlternatingReducedWord_product_eq_or_eq_neg
-- name    : QEC.Coding.TannerLiftedProduct.exists_lpsAlternatingReducedWord_product_eq_or_eq_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:54:24.870209+00:00
-- url     : https://prove2.me/theorems/b157b4c1-48ba-4396-acf3-e27ce126e12e
-- title:
--   Tanner Lifted Product: exists lps Alternating Reduced Word product eq or eq neg
-- statement:
--   Every LPS-parity quaternion of norm `p^n` has an alternating normal
--   form, up to the harmless central sign.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L195-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L195-L260

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.exists_lpsAlternatingReducedWord_product_eq_or_eq_neg
    (a : LPSResiduePrime p) : ∀ (n : ℕ) (t : LPSQuaternion),
    t.norm = (p : ℤ) ^ n → t.HasLPSParity →
    ∃ word : LPSAlternatingReducedWord a.degreePrime.pos n,
      lpsAlternatingQuaternionProduct a n word = t ∨
        lpsAlternatingQuaternionProduct a n word = -t := by sorry
