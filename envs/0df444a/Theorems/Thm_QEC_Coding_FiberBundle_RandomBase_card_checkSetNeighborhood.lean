-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_checkSetNeighborhood
-- name    : QEC.Coding.FiberBundle.RandomBase.card_checkSetNeighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:38:46.481149+00:00
-- url     : https://prove2.me/theorems/b3c1ace3-1201-4aed-a060-dc58cc883325
-- title:
--   Random Base: card check Set Neighborhood
-- statement:
--   Exact cardinality partition of a selected check set's neighborhood.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L133-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L133-L141

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.card_checkSetNeighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    (checkSetNeighborhood sample S).card =
      (couniqueNeighbors sample S).card +
        (nonCouniqueNeighbors sample S).card := by sorry
