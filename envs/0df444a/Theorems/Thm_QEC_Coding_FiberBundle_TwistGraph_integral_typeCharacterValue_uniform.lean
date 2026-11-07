-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_integral_typeCharacterValue_uniform
-- name    : QEC.Coding.FiberBundle.TwistGraph.integral_typeCharacterValue_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:44.005453+00:00
-- url     : https://prove2.me/theorems/879cd1ae-b8b4-45e5-aae9-13f99d06eff0
-- title:
--   Twist Graph: integral type Character Value uniform
-- statement:
--   The exact mean of one uniform nonzero-shift contribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L209-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L209-L226

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.integral_typeCharacterValue_uniform
    {ell : Nat}
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    ∫ shiftIndex,
        typeCharacterValue frequency shiftIndex
      ∂(PMF.uniformOfFintype (Fin (ell - 1))).toMeasure =
      -2 / (ell - 1 : Real) := by sorry
