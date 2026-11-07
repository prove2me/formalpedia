-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_two_le_hammingWeight_cycleFiberCoboundary_of_normalized
-- name    : QEC.Coding.FiberBundle.two_le_hammingWeight_cycleFiberCoboundary_of_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:55:14.715377+00:00
-- url     : https://prove2.me/theorems/7c46ee47-2678-4dce-bb3b-6cbaf0662cc1
-- title:
--   Fiber Bundle: two le hamming Weight cycle Fiber Coboundary of normalized
-- statement:
--   Every nonzero normalized cycle-fiber word has coboundary weight at least two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L324-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L324-L331

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.two_le_hammingWeight_cycleFiberCoboundary_of_normalized
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n))
    (hf : f ≠ 0)
    (hhalf : 2 * HammingWeight f ≤ Fintype.card (ZMod n)) :
    2 ≤ HammingWeight (cycleFiberCoboundary n f) := by sorry
