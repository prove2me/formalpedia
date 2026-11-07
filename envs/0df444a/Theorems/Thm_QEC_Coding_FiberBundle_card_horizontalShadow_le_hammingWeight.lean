-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_horizontalShadow_le_hammingWeight
-- name    : QEC.Coding.FiberBundle.card_horizontalShadow_le_hammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:32:37.055747+00:00
-- url     : https://prove2.me/theorems/6d5d02ad-de7b-4fb2-ab7b-11238b51185c
-- title:
--   Fiber Bundle: card horizontal Shadow le hamming Weight
-- statement:
--   Every base cell in the horizontal shadow contributes at least one cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2813-L2833
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2813-L2833

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_horizontalShadow_le_hammingWeight
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    (horizontalShadow x).card ≤ HammingWeight (horizontalComponent x) := by sorry
