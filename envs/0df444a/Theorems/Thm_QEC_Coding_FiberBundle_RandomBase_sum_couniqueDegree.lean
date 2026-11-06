-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_couniqueDegree
-- name    : QEC.Coding.FiberBundle.RandomBase.sum_couniqueDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:46:00.030717+00:00
-- url     : https://prove2.me/theorems/cb78e2a0-5290-4bd6-b5c2-c233ef91d58a
-- title:
--   Random Base: sum counique Degree
-- statement:
--   Counique degrees double-count to exactly the number of counique variables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L285-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L285-L318

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.sum_couniqueDegree
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    (∑ a ∈ S, couniqueDegree sample S a) =
      (couniqueNeighbors sample S).card := by sorry
