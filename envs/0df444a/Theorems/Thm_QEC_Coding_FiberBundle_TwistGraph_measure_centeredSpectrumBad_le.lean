-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_measure_centeredSpectrumBad_le
-- name    : QEC.Coding.FiberBundle.TwistGraph.measure_centeredSpectrumBad_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:59:00.073196+00:00
-- url     : https://prove2.me/theorems/e9a06451-a870-4578-8ee9-49f5d3d5be20
-- title:
--   Twist Graph: measure centered Spectrum Bad le
-- statement:
--   Union bound over all nonzero Fourier frequencies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L503-L553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L503-L553

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.measure_centeredSpectrumBad_le
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)] :
    (RandomTwist.distribution r typeCount ell).toMeasure.real
        {sample | CenteredSpectrumBad sample} ≤
      2 * ell *
        Real.exp (-(typeCount : Real) / 20000000000) := by sorry
