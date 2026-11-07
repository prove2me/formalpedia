-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_measure_centeredCharacterSum_ge_le
-- name    : QEC.Coding.FiberBundle.TwistGraph.measure_centeredCharacterSum_ge_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:24.082235+00:00
-- url     : https://prove2.me/theorems/0c9626e3-4622-48da-9e02-596228de8704
-- title:
--   Twist Graph: measure centered Character Sum ge le
-- statement:
--   One-sided Hoeffding bound for the centered multiplier at a fixed
--   nonzero frequency.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L363-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L363-L391

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.measure_centeredCharacterSum_ge_le
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (RandomTwist.distribution r typeCount ell).toMeasure.real
        {sample |
          (typeCount : Real) / 50000 ≤
            centeredCharacterSum frequency sample} ≤
      Real.exp (-(typeCount : Real) / 20000000000) := by sorry
