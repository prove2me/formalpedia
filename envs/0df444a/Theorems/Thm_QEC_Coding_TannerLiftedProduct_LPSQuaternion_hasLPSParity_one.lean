-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternion_hasLPSParity_one
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternion.hasLPSParity_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:46:06.627024+00:00
-- url     : https://prove2.me/theorems/0d0e6d42-d147-4ce5-b59b-3bcaea752f7e
-- title:
--   LPSQuaternion: has LPSParity one
-- statement:
--   The LPSQuaternion construction uses the has LPSParity one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L26-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L26-L28

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternion.hasLPSParity_one :
    (1 : LPSQuaternion).HasLPSParity := by sorry
