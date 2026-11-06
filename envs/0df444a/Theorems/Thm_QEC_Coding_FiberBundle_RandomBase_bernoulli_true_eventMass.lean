-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_bernoulli_true_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.bernoulli_true_eventMass
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:46:50.550209+00:00
-- url     : https://prove2.me/theorems/2a0ee8b8-c8d2-4c08-af44-7bdb32b5493c
-- title:
--   Random Base: bernoulli true event Mass
-- statement:
--   The sure event under one Bernoulli coordinate has mass one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L461-L472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L461-L472

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.bernoulli_true_eventMass
    (p : NNReal) (hp : p ≤ 1) :
    eventMass (PMF.bernoulli p hp) (fun _bit => True) = 1 := by sorry
