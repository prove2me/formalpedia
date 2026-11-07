-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_verticalShadow_le_hammingWeight
-- name    : QEC.Coding.FiberBundle.card_verticalShadow_le_hammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:32:52.98532+00:00
-- url     : https://prove2.me/theorems/a516462b-516a-47d2-870f-16469efa555d
-- title:
--   Fiber Bundle: card vertical Shadow le hamming Weight
-- statement:
--   Every base cell in the vertical shadow contributes at least one cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2836-L2856
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2836-L2856

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_verticalShadow_le_hammingWeight
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    (verticalShadow x).card ≤ HammingWeight (verticalComponent x) := by sorry
