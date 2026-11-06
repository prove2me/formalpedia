-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalFiber_le_horizontalComponent
-- name    : QEC.Coding.FiberBundle.hammingWeight_horizontalFiber_le_horizontalComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:53:04.444422+00:00
-- url     : https://prove2.me/theorems/03490946-a922-41ff-8f0c-def841eaee33
-- title:
--   Fiber Bundle: hamming Weight horizontal Fiber le horizontal Component
-- statement:
--   One horizontal fiber contributes no more weight than the whole horizontal sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1689-L1699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1689-L1699

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_horizontalFiber_le_horizontalComponent
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (b : baseOne) :
    HammingWeight (horizontalFiber x b) ≤
      HammingWeight (horizontalComponent x) := by sorry
