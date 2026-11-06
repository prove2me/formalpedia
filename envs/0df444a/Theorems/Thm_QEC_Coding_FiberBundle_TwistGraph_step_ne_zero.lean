-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_step_ne_zero
-- name    : QEC.Coding.FiberBundle.TwistGraph.step_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:43:23.629125+00:00
-- url     : https://prove2.me/theorems/8b29d948-6ad3-43c1-9c87-81f49064527f
-- title:
--   Twist Graph: step ne zero
-- statement:
--   Sampled type steps are genuinely nonzero modulo `ell`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L229-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L229-L238

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.step_ne_zero
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) :
    step sample τ ≠ 0 := by sorry
