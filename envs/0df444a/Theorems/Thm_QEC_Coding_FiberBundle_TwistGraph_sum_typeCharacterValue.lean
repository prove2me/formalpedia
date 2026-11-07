-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_typeCharacterValue
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_typeCharacterValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:35.62753+00:00
-- url     : https://prove2.me/theorems/76fe52b5-6871-41ea-b5d3-1e656304f18e
-- title:
--   Twist Graph: sum type Character Value
-- statement:
--   Exact sum of the real undirected contributions over all nonzero shifts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L176-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L176-L206

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.sum_typeCharacterValue
    {ell : Nat}
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (∑ shiftIndex : Fin (ell - 1),
        typeCharacterValue frequency shiftIndex) = -2 := by sorry
