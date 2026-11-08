-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22_rateCoefficient_bound
-- name    : QEC.Coding.TannerLiftedProduct.pk22_rateCoefficient_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:29:02.203237+00:00
-- url     : https://prove2.me/theorems/b5ed4c12-b731-415f-998c-82c57f175ab9
-- title:
--   Tanner Lifted Product: pk22 rate Coefficient bound
-- statement:
--   The concrete local dimensions meet any requested rate below one once
--   the exponential index is large enough.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L164-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L164-L206

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22_rateCoefficient_bound
    (q t : Nat) (hq : 2 ≤ q) (rate : ℝ) (hRate : rate < 1)
    (hLarge : (4 * 124421 : ℝ) <
      (1 - rate) * ((q ^ t : Nat) : ℝ)) :
    2 * ((pk22RowCoefficient q t : ℝ) + pk22RowCoefficient q t) *
        pk22LocalWidth q t ≤
      (1 - rate) *
        ((pk22LocalWidth q t : ℝ) ^ 2 +
          4 * (pk22RowCoefficient q t : ℝ) * pk22RowCoefficient q t) := by sorry
