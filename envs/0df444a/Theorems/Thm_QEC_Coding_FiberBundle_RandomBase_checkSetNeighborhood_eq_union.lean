-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_checkSetNeighborhood_eq_union
-- name    : QEC.Coding.FiberBundle.RandomBase.checkSetNeighborhood_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:37:50.871168+00:00
-- url     : https://prove2.me/theorems/cb94d97f-5515-495d-a57e-cff23feb2749
-- title:
--   Random Base: check Set Neighborhood eq union
-- statement:
--   Every neighbor is either counique or non-counique.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L122-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L122-L130

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.checkSetNeighborhood_eq_union
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    checkSetNeighborhood sample S =
      couniqueNeighbors sample S ∪ nonCouniqueNeighbors sample S := by sorry
