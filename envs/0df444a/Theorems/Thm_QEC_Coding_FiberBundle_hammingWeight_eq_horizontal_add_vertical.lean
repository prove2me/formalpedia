-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_horizontal_add_vertical
-- name    : QEC.Coding.FiberBundle.hammingWeight_eq_horizontal_add_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:54:35.901224+00:00
-- url     : https://prove2.me/theorems/3f967f20-489a-45a3-a47a-34d4003c3875
-- title:
--   Fiber Bundle: hamming Weight eq horizontal add vertical
-- statement:
--   Total Hamming weight is the exact sum of horizontal and vertical weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1392-L1403
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1392-L1403

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_eq_horizontal_add_vertical
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype baseOne]
    [Fintype fiberZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight x =
      HammingWeight (horizontalComponent x) +
        HammingWeight (verticalComponent x) := by sorry
