-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_two_le_hammingWeight_of_sum_eq_zero_of_ne_zero
-- name    : QEC.Coding.FiberBundle.two_le_hammingWeight_of_sum_eq_zero_of_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:54:57.705335+00:00
-- url     : https://prove2.me/theorems/90c533fe-c780-47ce-b0de-e550f472722f
-- title:
--   Fiber Bundle: two le hamming Weight of sum eq zero of ne zero
-- statement:
--   A nonzero binary word with zero total parity has at least two nonzero
--   coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L171-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L171-L203

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.two_le_hammingWeight_of_sum_eq_zero_of_ne_zero
    {ι : Type u} [Fintype ι]
    (x : Word (ZMod 2) ι)
    (hsum : (∑ i : ι, x i) = 0)
    (hx : x ≠ 0) :
    2 ≤ HammingWeight x := by sorry
