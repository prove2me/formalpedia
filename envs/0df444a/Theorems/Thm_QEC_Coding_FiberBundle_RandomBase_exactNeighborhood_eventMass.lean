-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exactNeighborhood_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.exactNeighborhood_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:50:38.523207+00:00
-- url     : https://prove2.me/theorems/1a5cbcea-a56a-4715-905b-c800ebe31ac7
-- title:
--   Random Base: exact Neighborhood event Mass
-- statement:
--   Exact probability that `S` has variable neighborhood exactly `T`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L597-L686
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L597-L686

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.exactNeighborhood_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T) =
      (1 -
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ T.card *
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        S.card) ^ (4 * r - T.card) := by sorry
