-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_cycleFiberPrimitive
-- name    : QEC.Coding.FiberBundle.cycleFiberCoboundary_cycleFiberPrimitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:07:14.7632+00:00
-- url     : https://prove2.me/theorems/7274a378-820a-4513-a27b-b741ce523ea7
-- title:
--   Fiber Bundle: cycle Fiber Coboundary cycle Fiber Primitive
-- statement:
--   Every zero-parity binary cochain on a nondegenerate cycle is the coboundary
--   of its explicit prefix-sum primitive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L42-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L42-L108

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.cycleFiberCoboundary_cycleFiberPrimitive
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (g : Word (ZMod 2) (ZMod n))
    (hg : (∑ j : ZMod n, g j) = 0) :
    cycleFiberCoboundary n (cycleFiberPrimitive n g) = g := by sorry
