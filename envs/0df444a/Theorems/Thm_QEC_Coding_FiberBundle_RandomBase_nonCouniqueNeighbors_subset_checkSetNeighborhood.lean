-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nonCouniqueNeighbors_subset_checkSetNeighborhood
-- name    : QEC.Coding.FiberBundle.RandomBase.nonCouniqueNeighbors_subset_checkSetNeighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:10:58.409716+00:00
-- url     : https://prove2.me/theorems/c437085b-0265-489e-85b6-621cdd8be9d3
-- title:
--   Random Base: non Counique Neighbors subset check Set Neighborhood
-- statement:
--   Non-counique neighbors are neighbors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L99-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L99-L108

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.nonCouniqueNeighbors_subset_checkSetNeighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    nonCouniqueNeighbors sample S ⊆ checkSetNeighborhood sample S := by sorry
