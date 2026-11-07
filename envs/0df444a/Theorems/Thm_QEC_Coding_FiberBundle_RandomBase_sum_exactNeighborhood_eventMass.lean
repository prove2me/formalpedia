-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_exactNeighborhood_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.sum_exactNeighborhood_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:56:38.087921+00:00
-- url     : https://prove2.me/theorems/ea629074-3178-427b-a1fa-01a2dca85fcf
-- title:
--   Random Base: sum exact Neighborhood event Mass
-- statement:
--   The exact-neighborhood events form a probability partition for every fixed
--   check set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L743-L762
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L743-L762

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.sum_exactNeighborhood_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) :
    (∑ T : Finset (Fin (4 * r)),
        eventMass
          (distribution r Delta hDelta)
          (fun sample => checkSetNeighborhood sample S = T)) = 1 := by sorry
