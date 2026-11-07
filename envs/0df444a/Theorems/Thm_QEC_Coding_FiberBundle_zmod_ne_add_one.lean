-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_zmod_ne_add_one
-- name    : QEC.Coding.FiberBundle.zmod_ne_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:54:38.961544+00:00
-- url     : https://prove2.me/theorems/5cf1dae0-04f8-4777-add0-3ed5f638a74c
-- title:
--   Fiber Bundle: zmod ne add one
-- statement:
--   A cycle of length at least two has distinct consecutive vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L206-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L206-L215

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.zmod_ne_add_one
    (n : Nat) [NeZero n] (hn : 2 ≤ n) (j : ZMod n) :
    j ≠ j + 1 := by sorry
