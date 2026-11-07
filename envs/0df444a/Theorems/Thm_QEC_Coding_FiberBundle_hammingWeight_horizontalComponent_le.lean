-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_le
-- name    : QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:45:52.960714+00:00
-- url     : https://prove2.me/theorems/07df9d1e-7a22-4bce-b958-d49e394ad103
-- title:
--   Fiber Bundle: hamming Weight horizontal Component le
-- statement:
--   Horizontal weight is bounded by the total bundle one-chain weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L820-L828
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L820-L828

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_le
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype baseOne]
    [Fintype fiberZero] [Fintype fiberOne]
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (horizontalComponent z) ≤ HammingWeight z := by sorry
