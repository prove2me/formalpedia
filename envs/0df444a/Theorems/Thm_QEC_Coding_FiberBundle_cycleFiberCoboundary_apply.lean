-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_apply
-- name    : QEC.Coding.FiberBundle.cycleFiberCoboundary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:52:33.348634+00:00
-- url     : https://prove2.me/theorems/2875b371-5282-447c-9e92-d499fd82299f
-- title:
--   Fiber Bundle: cycle Fiber Coboundary apply
-- statement:
--   On a nondegenerate cycle, an edge coboundary is the sum of its endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L225-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L225-L239

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.cycleFiberCoboundary_apply
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n)) (j : ZMod n) :
    cycleFiberCoboundary n f j = f j + f (j + 1) := by sorry
