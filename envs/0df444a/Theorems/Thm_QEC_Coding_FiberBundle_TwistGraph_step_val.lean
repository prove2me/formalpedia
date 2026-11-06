-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_step_val
-- name    : QEC.Coding.FiberBundle.TwistGraph.step_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:42:44.993675+00:00
-- url     : https://prove2.me/theorems/598d5ff7-a37e-48d1-8d9e-bd6db7437a83
-- title:
--   Twist Graph: step val
-- statement:
--   The canonical representative of a type step lies in `1, ..., ell - 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L216-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L216-L226

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.step_val
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) :
    (step sample τ).val =
      (RandomTwist.typeTwist sample τ).val + 1 := by sorry
