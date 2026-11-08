-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22ParameterIndex
-- name    : QEC.Coding.TannerLiftedProduct.exists_pk22ParameterIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:29:18.073698+00:00
-- url     : https://prove2.me/theorems/b2098304-3aa7-4092-98c0-c124dec3b4db
-- title:
--   Tanner Lifted Product: exists pk22 Parameter Index
-- statement:
--   There is an exponential index simultaneously large enough for row fit,
--   positive distance, and an arbitrary target rate below one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L210-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L210-L230

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.exists_pk22ParameterIndex
    (q : Nat) (hq : 2 ≤ q) (rate : ℝ) (hRate : rate < 1) :
    ∃ t : Nat,
      2 * 124421 ≤ q ^ t ∧
      23 ≤ q ^ t ∧
      (4 * 124421 : ℝ) < (1 - rate) * ((q ^ t : Nat) : ℝ) := by sorry
