-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nonCouniqueNeighbors_bound
-- name    : QEC.Coding.FiberBundle.RandomBase.nonCouniqueNeighbors_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:45:43.253232+00:00
-- url     : https://prove2.me/theorems/07f17985-3455-43da-b68c-887c1c73c8a9
-- title:
--   Random Base: non Counique Neighbors bound
-- statement:
--   Strong small-set expansion plus the degree window gives the paper's
--   `0.09 Delta |S|` non-counique-neighbor bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L247-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L247-L261

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.nonCouniqueNeighbors_bound
    {r Delta : Nat} {sample : Sample r}
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    100 * (nonCouniqueNeighbors sample S).card ≤
      9 * Delta * S.card := by sorry
