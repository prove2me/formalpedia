-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_hitProbability_lower_of_small
-- name    : QEC.Coding.FiberBundle.RandomBase.hitProbability_lower_of_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:53.390207+00:00
-- url     : https://prove2.me/theorems/926bf7bd-7e49-49f8-a2f6-077b24e2052e
-- title:
--   Random Base: hit Probability lower of small
-- statement:
--   For an HHO20-small check set, the probability that a variable is hit is at
--   least `399997 / 400000` times its first-order incidence load.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L383-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L383-L424

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.hitProbability_lower_of_small
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    (399997 : NNReal) / 400000 *
        ((S.card : NNReal) * incidenceProbability (4 * r) Delta) ≤
      1 -
        (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card := by sorry
