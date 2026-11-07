-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_distribution_typeTwist_hasLaw
-- name    : QEC.Coding.FiberBundle.TwistGraph.distribution_typeTwist_hasLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:29.756004+00:00
-- url     : https://prove2.me/theorems/1d098b3b-05fd-47b6-b6af-bd82bb9c66d4
-- title:
--   Twist Graph: distribution type Twist has Law
-- statement:
--   Every sampled type shift has the uniform nonzero-shift law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L264-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L264-L277

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.distribution_typeTwist_hasLaw
    (r typeCount ell : Nat)
    [NeZero (ell - 1)]
    (τ : Fin typeCount) :
    ProbabilityTheory.HasLaw
      (fun sample : RandomTwist.Sample r typeCount ell =>
        RandomTwist.typeTwist sample τ)
      (PMF.uniformOfFintype (Fin (ell - 1))).toMeasure
      (RandomTwist.distribution r typeCount ell).toMeasure := by sorry
