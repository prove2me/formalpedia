-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_disjoint_couniqueNeighbors_nonCouniqueNeighbors
-- name    : QEC.Coding.FiberBundle.RandomBase.disjoint_couniqueNeighbors_nonCouniqueNeighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:37:43.575394+00:00
-- url     : https://prove2.me/theorems/6d2d7170-43ec-48d9-b443-ae4babe28294
-- title:
--   Random Base: disjoint counique Neighbors non Counique Neighbors
-- statement:
--   The counique and non-counique neighbor sets are disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L111-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L111-L119

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.disjoint_couniqueNeighbors_nonCouniqueNeighbors
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    Disjoint (couniqueNeighbors sample S) (nonCouniqueNeighbors sample S) := by sorry
