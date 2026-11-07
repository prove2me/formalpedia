-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_homologyBaseProjection_le_horizontalComponent
-- name    : QEC.Coding.FiberBundle.hammingWeight_homologyBaseProjection_le_horizontalComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:45:39.828541+00:00
-- url     : https://prove2.me/theorems/59a4ce48-cb8f-4e9b-aea9-a7e62d28ddb3
-- title:
--   Fiber Bundle: hamming Weight homology Base Projection le horizontal Component
-- statement:
--   Projection support costs at most the full horizontal Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L795-L817
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L795-L817

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_homologyBaseProjection_le_horizontalComponent
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (homologyBaseProjection z) ≤
      HammingWeight (horizontalComponent z) := by sorry
