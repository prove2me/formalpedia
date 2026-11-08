-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22LocalWidth_log_le
-- name    : QEC.Coding.TannerLiftedProduct.pk22LocalWidth_log_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:07.067482+00:00
-- url     : https://prove2.me/theorems/5a6c45ad-2698-4c51-99bd-674b7a6e58b3
-- title:
--   Tanner Lifted Product: pk22 Local Width log le
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Local Width log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L73-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L73-L83

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22LocalWidth_log_le
    (q t : Nat) (hq : 2 ≤ q) :
    Nat.log q (pk22LocalWidth q t) ≤ 4 * t + 8 := by sorry
