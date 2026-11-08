-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternion_CoordinatesDvd_mul_right
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternion.CoordinatesDvd.mul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:51:20.111816+00:00
-- url     : https://prove2.me/theorems/1f8e8fac-f0bb-4a3c-af18-04f29a271c84
-- title:
--   Coordinates Dvd: mul right
-- statement:
--   The Coordinates Dvd construction uses the mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L23-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L23-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternion.CoordinatesDvd.mul_right
    {s : ℤ} {t : LPSQuaternion} (ht : t.CoordinatesDvd s)
    (u : LPSQuaternion) : (t * u).CoordinatesDvd s := by sorry
