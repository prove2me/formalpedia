-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_twice_hammingWeight_normalizeBinaryWord_le_card
-- name    : QEC.Coding.FiberBundle.twice_hammingWeight_normalizeBinaryWord_le_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:55:31.430432+00:00
-- url     : https://prove2.me/theorems/a9edbd82-749b-4c8a-9132-d71466b27e0b
-- title:
--   Fiber Bundle: twice hamming Weight normalize Binary Word le card
-- statement:
--   The normalized binary representative occupies at most half the coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L392-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L392-L400

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.twice_hammingWeight_normalizeBinaryWord_le_card
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    2 * HammingWeight (normalizeBinaryWord x) ≤ Fintype.card ι := by sorry
