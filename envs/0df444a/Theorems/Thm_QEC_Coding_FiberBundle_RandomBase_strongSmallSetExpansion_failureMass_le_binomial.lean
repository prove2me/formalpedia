-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_strongSmallSetExpansion_failureMass_le_binomial
-- name    : QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_binomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:50.081078+00:00
-- url     : https://prove2.me/theorems/c5468c57-03d9-4cc8-94e6-86726a253744
-- title:
--   Random Base: strong Small Set Expansion failure Mass le binomial
-- statement:
--   Explicit binomial bound for random-base strong-expansion failure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1220-L1260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1220-L1260

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_binomial
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      (1 +
        ENNReal.ofReal
          (Real.exp (-(Delta : Real) / 1000))) ^ (3 * r) - 1 := by sorry
