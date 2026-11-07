-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_distribution_typeTwist_iIndepFun
-- name    : QEC.Coding.FiberBundle.TwistGraph.distribution_typeTwist_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:47.909124+00:00
-- url     : https://prove2.me/theorems/27a16ada-68f2-407b-a67a-dbe171a11215
-- title:
--   Twist Graph: distribution type Twist i Indep Fun
-- statement:
--   The sampled type-shift coordinates are mutually independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L246-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L246-L261

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.distribution_typeTwist_iIndepFun
    (r typeCount ell : Nat)
    [NeZero (ell - 1)] :
    ProbabilityTheory.iIndepFun
      (fun τ (sample : RandomTwist.Sample r typeCount ell) =>
        RandomTwist.typeTwist sample τ)
      (RandomTwist.distribution r typeCount ell).toMeasure := by sorry
