-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_heavyLayerSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_heavyLayerSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:43:51.850274+00:00
-- url     : https://prove2.me/theorems/34a30812-0319-43ad-9106-3a6151664383
-- title:
--   Twist Graph: mem heavy Layer Set iff
-- statement:
--   The Twist Graph construction uses the mem heavy Layer Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L343-L352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L343-L352

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_heavyLayerSet_iff
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ heavyLayerSet Delta w ↔
      4 * (4 * r) ≤ Delta * HammingWeight (layerWord w u) := by sorry
