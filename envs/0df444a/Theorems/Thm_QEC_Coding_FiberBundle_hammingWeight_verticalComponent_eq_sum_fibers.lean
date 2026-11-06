-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalComponent_eq_sum_fibers
-- name    : QEC.Coding.FiberBundle.hammingWeight_verticalComponent_eq_sum_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:52:15.701115+00:00
-- url     : https://prove2.me/theorems/55d93645-85f5-4a73-acbc-279840ab2666
-- title:
--   Fiber Bundle: hamming Weight vertical Component eq sum fibers
-- statement:
--   Vertical weight is the sum of the weights of its fiber words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1860-L1871
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1860-L1871

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_verticalComponent_eq_sum_fibers
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (verticalComponent x) =
      ∑ a : baseZero, HammingWeight (verticalFiber x a) := by sorry
