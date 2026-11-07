-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exactNeighborhood_eventMass_le_hitBound
-- name    : QEC.Coding.FiberBundle.RandomBase.exactNeighborhood_eventMass_le_hitBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:48.232217+00:00
-- url     : https://prove2.me/theorems/6940f15e-1ee3-439a-a48d-02f22e02416f
-- title:
--   Random Base: exact Neighborhood event Mass le hit Bound
-- statement:
--   The exact-neighborhood mass exposes the occupancy penalty `(s p)^t` for the
--   `t` variables that must actually be hit.  This is the factor absent from a
--   mere containment-event union bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1345-L1361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1345-L1361

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.exactNeighborhood_eventMass_le_hitBound
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T) ≤
      ((S.card : ENNReal) *
        (incidenceProbability (4 * r) Delta : ENNReal)) ^ T.card *
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        S.card) ^ (4 * r - T.card) := by sorry
