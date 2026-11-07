-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_strongSmallSetExpansion_failureMass_le_occupancy_sum
-- name    : QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_occupancy_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:59:39.423247+00:00
-- url     : https://prove2.me/theorems/352f4f54-9be1-4062-a7ed-4f90c1eac8cf
-- title:
--   Random Base: strong Small Set Expansion failure Mass le occupancy sum
-- statement:
--   Expansion failure is bounded by the occupancy-weighted witness sum.  The
--   factor involving `witness.1.2.card` records that every member of the proposed
--   neighborhood must be hit, while every variable outside it must be avoided.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1419-L1445
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1419-L1445

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_occupancy_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ witness : ExpansionWitness r Delta,
        ((witness.1.1.card : ENNReal) *
          (incidenceProbability (4 * r) Delta : ENNReal)) ^
            witness.1.2.card *
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          witness.1.1.card) ^ (4 * r - witness.1.2.card) := by sorry
