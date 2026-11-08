-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternion_HasLPSParity_mul
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternion.HasLPSParity.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:46:43.226011+00:00
-- url     : https://prove2.me/theorems/47c68c6d-04c6-4ffc-a622-36e8d09c3783
-- title:
--   Has LPSParity: mul
-- statement:
--   The LPS parity class is closed under quaternion multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L31-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L31-L50

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternion.HasLPSParity.mul
    {t u : LPSQuaternion} (ht : t.HasLPSParity)
    (hu : u.HasLPSParity) : (t * u).HasLPSParity := by sorry
