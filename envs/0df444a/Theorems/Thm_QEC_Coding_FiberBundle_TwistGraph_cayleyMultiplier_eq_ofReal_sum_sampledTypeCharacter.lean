-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_cayleyMultiplier_eq_ofReal_sum_sampledTypeCharacter
-- name    : QEC.Coding.FiberBundle.TwistGraph.cayleyMultiplier_eq_ofReal_sum_sampledTypeCharacter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:51.888209+00:00
-- url     : https://prove2.me/theorems/8b7cca47-520c-4a7a-a559-6fbbdb2fc0eb
-- title:
--   Twist Graph: cayley Multiplier eq of Real sum sampled Type Character
-- statement:
--   The complex Cayley multiplier is the real sum of the sampled
--   undirected character contributions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L588-L610
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L588-L610

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.cayleyMultiplier_eq_ofReal_sum_sampledTypeCharacter
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (frequency : ZMod ell) :
    cayleyMultiplier sample frequency =
      ((∑ τ : Fin typeCount,
        sampledTypeCharacter frequency τ sample : Real) : Complex) := by sorry
