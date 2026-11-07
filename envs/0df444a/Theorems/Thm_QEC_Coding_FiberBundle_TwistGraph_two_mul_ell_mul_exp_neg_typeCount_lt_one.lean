-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_two_mul_ell_mul_exp_neg_typeCount_lt_one
-- name    : QEC.Coding.FiberBundle.TwistGraph.two_mul_ell_mul_exp_neg_typeCount_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:38.293249+00:00
-- url     : https://prove2.me/theorems/be26a0bd-8bc9-45d6-ac16-f5f5f41dd01f
-- title:
--   Twist Graph: two mul ell mul exp neg type Count lt one
-- statement:
--   The HHO20 logarithmic number of sampled types makes the simultaneous
--   Fourier failure probability strictly smaller than one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L557-L584
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L557-L584

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.two_mul_ell_mul_exp_neg_typeCount_lt_one
    (typeCount ell : Nat)
    (hEll : 100001 ≤ ell)
    (hTypeCount :
      (40000000000 : Real) * Real.log (ell : Real) ≤
        (typeCount : Real)) :
    2 * ell *
        Real.exp (-(typeCount : Real) / 20000000000) <
      1 := by sorry
