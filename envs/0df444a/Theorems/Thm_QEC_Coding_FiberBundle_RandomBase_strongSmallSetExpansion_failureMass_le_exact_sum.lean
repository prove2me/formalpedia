-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_strongSmallSetExpansion_failureMass_le_exact_sum
-- name    : QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_exact_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:19:40.931616+00:00
-- url     : https://prove2.me/theorems/ca0d1253-c4fa-4fd4-8082-232d0cf3b9b2
-- title:
--   Random Base: strong Small Set Expansion failure Mass le exact sum
-- statement:
--   Expansion failure is bounded by the exact sum over all finite containment
--   witnesses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L615-L636
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L615-L636

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_exact_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ witness : ExpansionWitness r Delta,
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          (witness.1.1.card * (4 * r - witness.1.2.card))) := by sorry
