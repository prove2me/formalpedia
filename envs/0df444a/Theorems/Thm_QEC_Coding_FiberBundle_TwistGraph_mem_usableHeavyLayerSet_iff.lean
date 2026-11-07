-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableHeavyLayerSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_usableHeavyLayerSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:44:49.979208+00:00
-- url     : https://prove2.me/theorems/a93022b1-0abc-4aff-a7c1-12605c4f131d
-- title:
--   Twist Graph: mem usable Heavy Layer Set iff
-- statement:
--   The Twist Graph construction uses the mem usable Heavy Layer Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L519-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L519-L531

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_usableHeavyLayerSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ usableHeavyLayerSet Delta twistSample w ↔
      u ∈ heavyLayerSet Delta w ∧
        98 * typeCount ≤
          100 * (twoSidedLightTypeSet Delta twistSample w u).card := by sorry
