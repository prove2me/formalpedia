-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_typeCharacterValue_mem_Icc
-- name    : QEC.Coding.FiberBundle.TwistGraph.typeCharacterValue_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:58:23.615196+00:00
-- url     : https://prove2.me/theorems/5c04888f-c42f-4677-9995-f048d215337c
-- title:
--   Twist Graph: type Character Value mem Icc
-- statement:
--   Every undirected character contribution lies in the sharp interval
--   `[-2, 2]`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L230-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L230-L243

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.typeCharacterValue_mem_Icc
    {ell : Nat} [NeZero ell]
    (frequency : ZMod ell)
    (shiftIndex : Fin (ell - 1)) :
    typeCharacterValue frequency shiftIndex ∈ Set.Icc (-2 : Real) 2 := by sorry
