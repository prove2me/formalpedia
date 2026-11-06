-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_sum_cycleFiberCoboundary_eq_zero
-- name    : QEC.Coding.FiberBundle.sum_cycleFiberCoboundary_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:54:41.951353+00:00
-- url     : https://prove2.me/theorems/dfda32c6-f15d-458b-b3e7-6076186d2df8
-- title:
--   Fiber Bundle: sum cycle Fiber Coboundary eq zero
-- statement:
--   Every cycle-fiber coboundary has zero total binary parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L242-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L242-L257

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.sum_cycleFiberCoboundary_eq_zero
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n)) :
    (∑ j : ZMod n, cycleFiberCoboundary n f j) = 0 := by sorry
