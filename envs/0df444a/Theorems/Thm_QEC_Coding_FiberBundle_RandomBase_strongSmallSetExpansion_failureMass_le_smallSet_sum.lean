-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_strongSmallSetExpansion_failureMass_le_smallSet_sum
-- name    : QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_smallSet_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:34.400466+00:00
-- url     : https://prove2.me/theorems/5be4d459-625b-4219-b917-79875d41d8ce
-- title:
--   Random Base: strong Small Set Expansion failure Mass le small Set sum
-- statement:
--   Global strong-expansion failure is bounded by the sum of the fixed-set
--   exponential tails.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1179-L1203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1179-L1203

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_smallSet_sum
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ S : SmallNonemptyCheckSet r Delta,
        ENNReal.ofReal
          (Real.exp (-((Delta : Real) * S.1.1.card / 1000))) := by sorry
