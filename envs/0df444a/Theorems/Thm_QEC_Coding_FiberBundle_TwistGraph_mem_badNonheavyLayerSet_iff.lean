-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badNonheavyLayerSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:44:31.558863+00:00
-- url     : https://prove2.me/theorems/69189305-e52a-42c5-931a-8a2e8ec68b18
-- title:
--   Twist Graph: mem bad Nonheavy Layer Set iff
-- statement:
--   The Twist Graph construction uses the mem bad Nonheavy Layer Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L491-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L491-L502

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ badNonheavyLayerSet Delta twistSample w ↔
      u ∈ nonheavyLayerSet Delta w ∧
        u ∉ usableNonheavyLayerSet Delta twistSample w := by sorry
