-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_binaryComplement
-- name    : QEC.Coding.FiberBundle.card_le_twice_hammingWeight_binaryComplement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:53:33.274143+00:00
-- url     : https://prove2.me/theorems/eb2d530a-f6f5-4926-b348-33998b025efd
-- title:
--   Fiber Bundle: card le twice hamming Weight binary Complement
-- statement:
--   If a binary fiber word occupies at most half the coordinates (in doubled
--   integer form), its complement occupies at least half.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L375-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L375-L380

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_le_twice_hammingWeight_binaryComplement
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι)
    (hx : 2 * HammingWeight x ≤ Fintype.card ι) :
    Fintype.card ι ≤ 2 * HammingWeight (binaryComplement x) := by sorry
