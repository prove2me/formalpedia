-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_ofReal_exp_card_eq_pow
-- name    : QEC.Coding.FiberBundle.RandomBase.ofReal_exp_card_eq_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:59.100636+00:00
-- url     : https://prove2.me/theorems/43f17767-e3e5-4148-a0e7-71095a3438c1
-- title:
--   Random Base: of Real exp card eq pow
-- statement:
--   The fixed-set exponential tail is geometric in the set cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1206-L1215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1206-L1215

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.ofReal_exp_card_eq_pow (Delta cardinality : Nat) :
    ENNReal.ofReal
        (Real.exp (-((Delta : Real) * cardinality / 1000))) =
      (ENNReal.ofReal
        (Real.exp (-(Delta : Real) / 1000))) ^ cardinality := by sorry
