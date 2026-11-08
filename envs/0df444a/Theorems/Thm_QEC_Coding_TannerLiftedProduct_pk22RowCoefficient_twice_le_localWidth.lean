-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22RowCoefficient_twice_le_localWidth
-- name    : QEC.Coding.TannerLiftedProduct.pk22RowCoefficient_twice_le_localWidth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:59.050609+00:00
-- url     : https://prove2.me/theorems/cf3845bd-547f-4623-b3b0-f47a8771037a
-- title:
--   Tanner Lifted Product: pk22 Row Coefficient twice le local Width
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Row Coefficient twice le local Width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L141-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L141-L160

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22RowCoefficient_twice_le_localWidth
    (q t : Nat) (hq : 2 ≤ q)
    (hLarge : 2 * 124421 ≤ q ^ t) :
    2 * pk22RowCoefficient q t ≤ pk22LocalWidth q t := by sorry
