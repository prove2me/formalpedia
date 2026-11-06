-- Prove2me | Theorems.Thm_QEC_Coding_not_mem_carrier_of_hammingWeight_lt_minimumDistance
-- name    : QEC.Coding.not_mem_carrier_of_hammingWeight_lt_minimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:21:12.940618+00:00
-- url     : https://prove2.me/theorems/a9ef778b-3493-4e68-b014-b097bce7a1dc
-- title:
--   Coding: not mem carrier of hamming Weight lt minimum Distance
-- statement:
--   No nonzero codeword has Hamming weight strictly below a proved minimum
--   distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L454-L460
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L454-L460

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem QEC.Coding.not_mem_carrier_of_hammingWeight_lt_minimumDistance {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι] {C : LinearCode F ι} {d : Nat}
    (hmin : MinimumDistance C d) {x : Word F ι} (hx0 : x ≠ 0) (hlt : HammingWeight x < d) :
    x ∉ C.carrier := by sorry
