-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22RowCoefficient_le
-- name    : QEC.Coding.TannerLiftedProduct.pk22RowCoefficient_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:15:44.458284+00:00
-- url     : https://prove2.me/theorems/d07e1960-0524-48f7-9649-5ecce5c469d9
-- title:
--   Tanner Lifted Product: pk22 Row Coefficient le
-- statement:
--   The concrete row count is bounded by a cubic field-size power.  This
--   explicit bound is the quantitative reason its ratio to the fourth-power
--   local width tends to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L99-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L99-L125

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22RowCoefficient_le
    (q t : Nat) (hq : 2 ≤ q) :
    pk22RowCoefficient q t ≤ 124421 * q ^ (3 * t) := by sorry
