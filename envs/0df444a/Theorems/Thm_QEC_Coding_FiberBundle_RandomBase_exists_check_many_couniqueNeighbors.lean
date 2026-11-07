-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_check_many_couniqueNeighbors
-- name    : QEC.Coding.FiberBundle.RandomBase.exists_check_many_couniqueNeighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:46:22.143449+00:00
-- url     : https://prove2.me/theorems/c6911572-39d7-4700-8fdf-d3fb01fc4918
-- title:
--   Random Base: exists check many counique Neighbors
-- statement:
--   Every nonempty sufficiently small check set contains a check with more than
--   `0.81 Delta` counique neighbors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L324-L351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L324-L351

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.exists_check_many_couniqueNeighbors
    {r Delta : Nat} {sample : Sample r}
    (hDelta : 0 < Delta)
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r))) (hS : S.Nonempty)
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    ∃ a ∈ S, 81 * Delta < 100 * couniqueDegree sample S a := by sorry
