-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_bernoulli_false_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.bernoulli_false_eventMass
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:46:38.263517+00:00
-- url     : https://prove2.me/theorems/2d907046-d846-43bb-8765-39e76a6f0d30
-- title:
--   Random Base: bernoulli false event Mass
-- statement:
--   Mass of the `false` outcome of the construction's Bernoulli coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L450-L458
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L450-L458

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.bernoulli_false_eventMass
    (p : NNReal) (hp : p ≤ 1) :
    eventMass (PMF.bernoulli p hp) (fun bit => bit = false) =
      ((1 - p : NNReal) : ENNReal) := by sorry
