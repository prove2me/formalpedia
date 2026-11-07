-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_mul_incidenceProbability_le_of_small
-- name    : QEC.Coding.FiberBundle.RandomBase.card_mul_incidenceProbability_le_of_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:50:40.745223+00:00
-- url     : https://prove2.me/theorems/de5e4010-e7b8-4ac1-bcdd-f46fa06b5fff
-- title:
--   Random Base: card mul incidence Probability le of small
-- statement:
--   The HHO20 small-set cutoff forces the expected incidence load of a selected
--   check set below `3 / 400000`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L357-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L357-L377

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.card_mul_incidenceProbability_le_of_small
    (r Delta : Nat) (hr : 0 < r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    (S.card : NNReal) * incidenceProbability (4 * r) Delta ≤
      (3 : NNReal) / 400000 := by sorry
