-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_sampledTypeCharacter_eq_centeredCharacterSum_sub
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_sampledTypeCharacter_eq_centeredCharacterSum_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:50.012814+00:00
-- url     : https://prove2.me/theorems/8f4c8899-48f1-42d1-b02e-9413ec7706aa
-- title:
--   Twist Graph: sum sampled Type Character eq centered Character Sum sub
-- statement:
--   Removing the exact mean expresses the raw character sum as the
--   centered sum minus its deterministic bias.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L614-L626
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L614-L626

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.sum_sampledTypeCharacter_eq_centeredCharacterSum_sub
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (frequency : ZMod ell) :
    (∑ τ : Fin typeCount,
        sampledTypeCharacter frequency τ sample) =
      centeredCharacterSum frequency sample -
        2 * typeCount / (ell - 1 : Real) := by sorry
