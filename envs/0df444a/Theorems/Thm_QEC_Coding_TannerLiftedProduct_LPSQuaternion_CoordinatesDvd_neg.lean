-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternion_CoordinatesDvd_neg
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternion.CoordinatesDvd.neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:51:25.565352+00:00
-- url     : https://prove2.me/theorems/8895f4c8-d403-430f-b330-0e1feb3ce4e3
-- title:
--   Coordinates Dvd: neg
-- statement:
--   The Coordinates Dvd construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L16-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L16-L21

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternion.CoordinatesDvd.neg
    {s : ℤ} {t : LPSQuaternion} (ht : t.CoordinatesDvd s) :
    (-t).CoordinatesDvd s := by sorry
