-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_cycleFiberChainBoundary_le_two_mul
-- name    : QEC.Coding.FiberBundle.hammingWeight_cycleFiberChainBoundary_le_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:33.556192+00:00
-- url     : https://prove2.me/theorems/5170d977-26f0-4f56-b33c-753850701283
-- title:
--   Fiber Bundle: hamming Weight cycle Fiber Chain Boundary le two mul
-- statement:
--   A cyclic boundary has weight at most twice the word weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2480-L2509
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2480-L2509

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_cycleFiberChainBoundary_le_two_mul
    (n : Nat) [NeZero n] [NeZero (n - 1)]
    (v : Word (ZMod 2) (ZMod n)) :
    HammingWeight (cycleFiberChainBoundary n v) ≤
      2 * HammingWeight v := by sorry
