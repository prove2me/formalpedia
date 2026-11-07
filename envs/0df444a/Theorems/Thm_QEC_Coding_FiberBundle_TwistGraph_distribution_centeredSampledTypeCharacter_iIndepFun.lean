-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_distribution_centeredSampledTypeCharacter_iIndepFun
-- name    : QEC.Coding.FiberBundle.TwistGraph.distribution_centeredSampledTypeCharacter_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:57:16.593954+00:00
-- url     : https://prove2.me/theorems/d274c24a-b305-423a-8b4f-97e91e479fb5
-- title:
--   Twist Graph: distribution centered Sampled Type Character i Indep Fun
-- statement:
--   Centering by the exact deterministic mean preserves mutual
--   independence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L348-L359
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L348-L359

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.distribution_centeredSampledTypeCharacter_iIndepFun
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell) :
    ProbabilityTheory.iIndepFun
      (fun τ => centeredSampledTypeCharacter frequency τ)
      (RandomTwist.distribution r typeCount ell).toMeasure := by sorry
