-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_eq_sum_fibers
-- name    : QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_eq_sum_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:52:04.200789+00:00
-- url     : https://prove2.me/theorems/1fa11d2e-e051-45b0-99ea-d161fb82accd
-- title:
--   Fiber Bundle: hamming Weight horizontal Component eq sum fibers
-- statement:
--   Horizontal weight is the sum of the weights of its fiber words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1406-L1417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1406-L1417

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_eq_sum_fibers
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (horizontalComponent x) =
      ∑ b : baseOne, HammingWeight (horizontalFiber x b) := by sorry
