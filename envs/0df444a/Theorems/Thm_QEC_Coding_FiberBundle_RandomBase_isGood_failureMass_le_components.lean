-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_isGood_failureMass_le_components
-- name    : QEC.Coding.FiberBundle.RandomBase.isGood_failureMass_le_components
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:44:50.915919+00:00
-- url     : https://prove2.me/theorems/ee002301-7cd4-43f1-8956-a6191d08cab5
-- title:
--   Random Base: is Good failure Mass le components
-- statement:
--   The three random-base conclusions fail only if the degree, full-rank, or
--   linear-distance component fails.  This is the probability-level conjunction
--   bridge used before instantiating the explicit tail bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L982-L1019
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L982-L1019

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.isGood_failureMass_le_components
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample => IsGood (Delta := Delta) sample) ≤
      failureMass
          (distribution r Delta hDelta)
          (fun sample => HasDegreeWindows (Delta := Delta) sample) +
        failureMass
          (distribution r Delta hDelta)
          (@HasFullRowRank r) +
        failureMass
          (distribution r Delta hDelta)
          (@HasLinearDistance r) := by sorry
