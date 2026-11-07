-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badHeavyLayerSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_badHeavyLayerSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:36.332198+00:00
-- url     : https://prove2.me/theorems/27a58069-2a41-4048-835d-f31e30975dda
-- title:
--   Twist Graph: mem bad Heavy Layer Set iff
-- statement:
--   The Twist Graph construction uses the mem bad Heavy Layer Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L408-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L408-L419

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_badHeavyLayerSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ badHeavyLayerSet Delta twistSample w ↔
      u ∈ heavyLayerSet Delta w ∧
        u ∉ usableHeavyLayerSet Delta twistSample w := by sorry
