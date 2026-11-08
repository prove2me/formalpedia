-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScaleQuaternion_neg
-- name    : QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:48:30.00055+00:00
-- url     : https://prove2.me/theorems/384205c0-619e-4d01-a010-ee5a390e4eac
-- title:
--   Tanner Lifted Product: lps Scale Quaternion neg
-- statement:
--   The Tanner Lifted Product construction uses the lps Scale Quaternion neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L47-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L47-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_neg (s : ℤ) (t : LPSQuaternion) :
    lpsScaleQuaternion s (-t) = -lpsScaleQuaternion s t := by sorry
