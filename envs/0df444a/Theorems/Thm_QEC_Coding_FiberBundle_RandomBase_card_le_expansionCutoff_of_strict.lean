-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_le_expansionCutoff_of_strict
-- name    : QEC.Coding.FiberBundle.RandomBase.card_le_expansionCutoff_of_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:21.987557+00:00
-- url     : https://prove2.me/theorems/a0e85393-9b1a-4caa-a672-561b82853b89
-- title:
--   Random Base: card le expansion Cutoff of strict
-- statement:
--   The strict expansion failure inequality implies the integral cutoff event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1052-L1058
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1052-L1058

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.card_le_expansionCutoff_of_strict
    {r Delta : Nat} {S : Finset (Fin (3 * r))}
    {cardinality : Nat}
    (hStrict : 100 * cardinality < 92 * Delta * S.card) :
    cardinality ≤ expansionCutoff Delta S := by sorry
