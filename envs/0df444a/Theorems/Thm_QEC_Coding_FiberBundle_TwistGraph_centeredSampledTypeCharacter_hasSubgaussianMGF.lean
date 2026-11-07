-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_centeredSampledTypeCharacter_hasSubgaussianMGF
-- name    : QEC.Coding.FiberBundle.TwistGraph.centeredSampledTypeCharacter_hasSubgaussianMGF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:57:13.136867+00:00
-- url     : https://prove2.me/theorems/7de983c0-6c71-4e30-ad78-236c1113cf89
-- title:
--   Twist Graph: centered Sampled Type Character has Subgaussian MGF
-- statement:
--   Each centered sampled character coordinate is sub-Gaussian with
--   Hoeffding parameter `4`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L318-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L318-L344

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.centeredSampledTypeCharacter_hasSubgaussianMGF
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0)
    (τ : Fin typeCount) :
    ProbabilityTheory.HasSubgaussianMGF
      (centeredSampledTypeCharacter frequency τ)
      (4 : NNReal)
      (RandomTwist.distribution r typeCount ell).toMeasure := by sorry
