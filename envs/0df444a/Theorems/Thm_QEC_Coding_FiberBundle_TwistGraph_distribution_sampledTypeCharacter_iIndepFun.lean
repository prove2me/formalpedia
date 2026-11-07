-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_distribution_sampledTypeCharacter_iIndepFun
-- name    : QEC.Coding.FiberBundle.TwistGraph.distribution_sampledTypeCharacter_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:56.700908+00:00
-- url     : https://prove2.me/theorems/4ae1759d-c0bc-47c3-817b-ecb1011aad9d
-- title:
--   Twist Graph: distribution sampled Type Character i Indep Fun
-- statement:
--   The real character contributions remain mutually independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L280-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L280-L291

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.distribution_sampledTypeCharacter_iIndepFun
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell) :
    ProbabilityTheory.iIndepFun
      (fun τ => sampledTypeCharacter frequency τ)
      (RandomTwist.distribution r typeCount ell).toMeasure := by sorry
