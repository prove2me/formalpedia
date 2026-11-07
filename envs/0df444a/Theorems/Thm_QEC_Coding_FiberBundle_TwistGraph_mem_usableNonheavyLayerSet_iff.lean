-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableNonheavyLayerSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:44:33.659586+00:00
-- url     : https://prove2.me/theorems/9bf8ef36-f76f-465c-80c1-45b86255c77e
-- title:
--   Twist Graph: mem usable Nonheavy Layer Set iff
-- statement:
--   The Twist Graph construction uses the mem usable Nonheavy Layer Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L475-L488
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L475-L488

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ usableNonheavyLayerSet Delta twistSample w ↔
      u ∈ nonheavyLayerSet Delta w ∧
        typeCount ≤
          5 * neighborIncidenceCount twistSample
            (nonheavyLayerSet Delta w) u := by sorry
