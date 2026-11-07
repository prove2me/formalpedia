-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nineteen_twentieths_generatorBase_le_of_small
-- name    : QEC.Coding.FiberBundle.RandomBase.nineteen_twentieths_generatorBase_le_of_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:03.003061+00:00
-- url     : https://prove2.me/theorems/fc1dd2c2-8399-4f0c-a779-00eab5d5035e
-- title:
--   Random Base: nineteen twentieths generator Base le of small
-- statement:
--   At the test weight `19 / 20`, the fixed-set generating-function base has a
--   strict first-order deficit controlled by the selected incidence load.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L430-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L430-L490

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.nineteen_twentieths_generatorBase_le_of_small
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    (19 : NNReal) / 20 *
          (1 -
            (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card) +
        (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card ≤
      1 -
        (1 : NNReal) / 20 *
          ((399997 : NNReal) / 400000 *
            ((S.card : NNReal) *
              incidenceProbability (4 * r) Delta)) := by sorry
