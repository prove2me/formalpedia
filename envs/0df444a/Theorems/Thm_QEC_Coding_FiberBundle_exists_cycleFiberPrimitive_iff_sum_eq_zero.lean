-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_cycleFiberPrimitive_iff_sum_eq_zero
-- name    : QEC.Coding.FiberBundle.exists_cycleFiberPrimitive_iff_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:33:22.855211+00:00
-- url     : https://prove2.me/theorems/30fd2656-2bc3-4186-8e4f-5c32eb838d8c
-- title:
--   Fiber Bundle: exists cycle Fiber Primitive iff sum eq zero
-- statement:
--   Zero parity is exactly the image condition for the cycle coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L111-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L111-L121

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_cycleFiberPrimitive_iff_sum_eq_zero
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (g : Word (ZMod 2) (ZMod n)) :
    (∃ f, cycleFiberCoboundary n f = g) ↔
      (∑ j : ZMod n, g j) = 0 := by sorry
