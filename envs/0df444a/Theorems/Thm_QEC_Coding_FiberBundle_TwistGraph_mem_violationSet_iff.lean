-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_violationSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_violationSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:46:28.277779+00:00
-- url     : https://prove2.me/theorems/9c784d3a-0c44-467e-b6e0-5251d32d24a8
-- title:
--   Twist Graph: mem violation Set iff
-- statement:
--   The Twist Graph construction uses the mem violation Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L465-L475
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L465-L475

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_violationSet_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (a : Fin (3 * r)) :
    (u, a) ∈ violationSet baseSample twistSample w ↔
      checkSyndrome baseSample twistSample w u a ≠ 0 := by sorry
