-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_strongSmallSetExpansion_failureMass_le_exactNeighborhood_sum
-- name    : QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_exactNeighborhood_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:59:37.496619+00:00
-- url     : https://prove2.me/theorems/095cdf1a-8a70-4f0c-a144-012ad586201a
-- title:
--   Random Base: strong Small Set Expansion failure Mass le exact Neighborhood sum
-- statement:
--   Expansion failure is bounded by the exact-neighborhood occupancy sum.  This is
--   the finite probabilistic reduction used by the subsequent analytic estimate;
--   it has no externally supplied matrix or expansion certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1385-L1412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1385-L1412

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_exactNeighborhood_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ witness : ExpansionWitness r Delta,
        (1 -
          (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
            witness.1.1.card)) ^ witness.1.2.card *
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          witness.1.1.card) ^ (4 * r - witness.1.2.card) := by sorry
