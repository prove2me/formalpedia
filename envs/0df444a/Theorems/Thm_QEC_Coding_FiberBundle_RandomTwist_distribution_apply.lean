-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
-- name    : QEC.Coding.FiberBundle.RandomTwist.distribution_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:36:32.803845+00:00
-- url     : https://prove2.me/theorems/9f97a5b1-9a47-4974-bdc3-3828997b7222
-- title:
--   Random Twist: distribution apply
-- statement:
--   The Random Twist construction uses the distribution apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomTwist.lean#L100-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomTwist.lean#L100-L107

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomTwist
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomTwist.distribution_apply
    (r typeCount ell : Nat)
    [NeZero (ell - 1)]
    (sample : Sample r typeCount ell) :
    distribution r typeCount ell sample =
      ∏ i : ChoiceIndex r typeCount,
        coordinatePMF ell i (sample i) := by sorry

attribute [defeq] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
