-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coordinatesDvd_lpsScaleQuaternion
-- name    : QEC.Coding.TannerLiftedProduct.coordinatesDvd_lpsScaleQuaternion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:51:34.989992+00:00
-- url     : https://prove2.me/theorems/b882a91f-33eb-42c2-83e7-6c045e79b2a2
-- title:
--   Tanner Lifted Product: coordinates Dvd lps Scale Quaternion
-- statement:
--   The Tanner Lifted Product construction uses the coordinates Dvd lps Scale Quaternion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L43-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L43-L45

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coordinatesDvd_lpsScaleQuaternion (s : ℤ) (t : LPSQuaternion) :
    (lpsScaleQuaternion s t).CoordinatesDvd s := by sorry
