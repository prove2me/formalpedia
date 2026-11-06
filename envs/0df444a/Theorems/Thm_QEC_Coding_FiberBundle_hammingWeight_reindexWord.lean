-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_reindexWord
-- name    : QEC.Coding.FiberBundle.hammingWeight_reindexWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:52:12.378826+00:00
-- url     : https://prove2.me/theorems/2e0c1956-c918-4d7d-92b8-11ea6c540828
-- title:
--   Fiber Bundle: hamming Weight reindex Word
-- statement:
--   Coordinate reindexing preserves Hamming weight exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L340-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L340-L348

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_reindexWord
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : Word (ZMod 2) ι) :
    HammingWeight (reindexWord e x) = HammingWeight x := by sorry
