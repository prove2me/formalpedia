-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_typeViolationSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_typeViolationSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:44:58.094666+00:00
-- url     : https://prove2.me/theorems/b9db24e1-d258-4a33-9e4a-320c1e6126a3
-- title:
--   Twist Graph: mem type Violation Set iff
-- statement:
--   The Twist Graph construction uses the mem type Violation Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L70-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L70-L82

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_typeViolationSet_iff
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    a ∈ typeViolationSet baseSample twistSample τ y z ↔
      RandomTwist.checkType typeCount a = τ ∧
        pairCheckSyndrome baseSample twistSample y z a ≠ 0 := by sorry
