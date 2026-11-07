-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_translateBundleWord
-- name    : QEC.Coding.FiberBundle.hammingWeight_translateBundleWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:55.432367+00:00
-- url     : https://prove2.me/theorems/23e2d6ed-d2c6-4bf1-bc6a-535f7df7acd5
-- title:
--   Fiber Bundle: hamming Weight translate Bundle Word
-- statement:
--   Global fiber translation preserves total Hamming weight exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4501-L4509
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4501-L4509

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_translateBundleWord
    {baseZero baseOne : Type u}
    [Fintype baseZero] [Fintype baseOne]
    (n : Nat) [NeZero n] (t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n))) :
    HammingWeight (translateBundleWord n t z) = HammingWeight z := by sorry
