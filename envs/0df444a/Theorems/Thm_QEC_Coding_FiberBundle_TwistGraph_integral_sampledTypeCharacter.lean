-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_integral_sampledTypeCharacter
-- name    : QEC.Coding.FiberBundle.TwistGraph.integral_sampledTypeCharacter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:50.801205+00:00
-- url     : https://prove2.me/theorems/3a33ea26-971a-48f0-baa7-8b63f0a08082
-- title:
--   Twist Graph: integral sampled Type Character
-- statement:
--   Exact expectation of each sampled character coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L294-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L294-L314

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.integral_sampledTypeCharacter
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0)
    (τ : Fin typeCount) :
    ∫ sample,
        sampledTypeCharacter frequency τ sample
      ∂(RandomTwist.distribution r typeCount ell).toMeasure =
      -2 / (ell - 1 : Real) := by sorry
