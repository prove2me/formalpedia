-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_isFullyGood_failureMass_le_components
-- name    : QEC.Coding.FiberBundle.RandomBase.isFullyGood_failureMass_le_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:41.663074+00:00
-- url     : https://prove2.me/theorems/d5e1a3f8-b45e-4c1d-aa24-5ab06773231d
-- title:
--   Random Base: is Fully Good failure Mass le components
-- statement:
--   Failure of `IsFullyGood` is covered by its old and expansion components.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1278-L1300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1278-L1300

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.isFullyGood_failureMass_le_components
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample => IsFullyGood (Delta := Delta) sample) ≤
      failureMass
          (distribution r Delta hDelta)
          (fun sample => IsGood (Delta := Delta) sample) +
        failureMass
          (distribution r Delta hDelta)
          (fun sample =>
            HasStrongSmallSetExpansion (Delta := Delta) sample) := by sorry
