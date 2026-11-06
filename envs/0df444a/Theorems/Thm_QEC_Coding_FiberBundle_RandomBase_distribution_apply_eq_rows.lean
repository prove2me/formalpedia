-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply_eq_rows
-- name    : QEC.Coding.FiberBundle.RandomBase.distribution_apply_eq_rows
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:34:34.552372+00:00
-- url     : https://prove2.me/theorems/f28630e4-0068-4329-9753-41b284114c41
-- title:
--   Random Base: distribution apply eq rows
-- statement:
--   Regrouping by rows preserves the original sampler pointwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L73-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L73-L81

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.distribution_apply_eq_rows
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (sample : Sample r) :
    distribution r Delta hDelta sample =
      rowGroupedDistribution r Delta hDelta (sampleEquivRows r sample) := by sorry
