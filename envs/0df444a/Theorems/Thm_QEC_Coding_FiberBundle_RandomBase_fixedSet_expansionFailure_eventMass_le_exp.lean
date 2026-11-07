-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_fixedSet_expansionFailure_eventMass_le_exp
-- name    : QEC.Coding.FiberBundle.RandomBase.fixedSet_expansionFailure_eventMass_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:43.491195+00:00
-- url     : https://prove2.me/theorems/9ba13fe5-a849-483d-a7f1-00121de4ea3a
-- title:
--   Random Base: fixed Set expansion Failure event Mass le exp
-- statement:
--   For every fixed HHO20-small check set, failure of `0.92 Δ` neighborhood
--   expansion has mass at most `exp(-Δ |S| / 1000)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1112-L1133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1112-L1133

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.fixedSet_expansionFailure_eventMass_le_exp
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          100 * (checkSetNeighborhood sample S).card <
            92 * Delta * S.card) ≤
      ENNReal.ofReal
        (Real.exp (-((Delta : Real) * S.card / 1000))) := by sorry
