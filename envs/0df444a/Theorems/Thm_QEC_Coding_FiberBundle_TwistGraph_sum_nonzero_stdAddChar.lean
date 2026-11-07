-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_nonzero_stdAddChar
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_nonzero_stdAddChar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:28.691435+00:00
-- url     : https://prove2.me/theorems/d40df5b2-cacc-4fc8-aad9-f2e5a78cb182
-- title:
--   Twist Graph: sum nonzero std Add Char
-- statement:
--   The nonzero representatives `1, ..., ell - 1` have character sum `-1` at
--   every nonzero frequency.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L111-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L111-L173

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.sum_nonzero_stdAddChar
    {ell : Nat}
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (∑ shiftIndex : Fin (ell - 1),
        ZMod.stdAddChar
          (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)) =
      -1 := by sorry
