-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_sum_indicator
-- name    : QEC.Coding.FiberBundle.hammingWeight_eq_sum_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:51:54.625949+00:00
-- url     : https://prove2.me/theorems/a7f29607-d2cc-4721-bd42-d9a78013b2c7
-- title:
--   Fiber Bundle: hamming Weight eq sum indicator
-- statement:
--   Hamming weight as a sum of coordinatewise nonzero indicators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L161-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L161-L165

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_eq_sum_indicator
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    HammingWeight x = ∑ i : ι, if x i ≠ 0 then 1 else 0 := by sorry
