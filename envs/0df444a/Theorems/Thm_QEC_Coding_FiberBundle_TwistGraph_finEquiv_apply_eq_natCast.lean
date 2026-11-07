-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_finEquiv_apply_eq_natCast
-- name    : QEC.Coding.FiberBundle.TwistGraph.finEquiv_apply_eq_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:40.244939+00:00
-- url     : https://prove2.me/theorems/fa350a29-980b-41b5-b1b7-aca3aab9d978
-- title:
--   Twist Graph: fin Equiv apply eq nat Cast
-- statement:
--   The Twist Graph construction uses the fin Equiv apply eq nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L96-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L96-L105

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.finEquiv_apply_eq_natCast
    {ell : Nat} [NeZero ell] (i : Fin ell) :
    (ZMod.finEquiv ell) i = (i.val : ZMod ell) := by sorry
