-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_measure_centeredFrequencyBad_le
-- name    : QEC.Coding.FiberBundle.TwistGraph.measure_centeredFrequencyBad_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:39.62347+00:00
-- url     : https://prove2.me/theorems/8584611b-1abe-45d8-bad1-50320e5baaed
-- title:
--   Twist Graph: measure centered Frequency Bad le
-- statement:
--   Two-sided fixed-frequency failure probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L449-L500
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L449-L500

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.measure_centeredFrequencyBad_le
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (RandomTwist.distribution r typeCount ell).toMeasure.real
        {sample | CenteredFrequencyBad frequency sample} ≤
      2 * Real.exp (-(typeCount : Real) / 20000000000) := by sorry
