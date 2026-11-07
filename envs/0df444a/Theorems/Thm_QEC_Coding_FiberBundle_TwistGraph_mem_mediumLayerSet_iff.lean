-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_mediumLayerSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_mediumLayerSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:43:47.715122+00:00
-- url     : https://prove2.me/theorems/41954404-4ec0-45bd-978e-e962e1289dfa
-- title:
--   Twist Graph: mem medium Layer Set iff
-- statement:
--   The Twist Graph construction uses the mem medium Layer Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L330-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L330-L340

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_mediumLayerSet_iff
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ mediumLayerSet Delta w ↔
      2 * (4 * r) < Delta * HammingWeight (layerWord w u) ∧
        Delta * HammingWeight (layerWord w u) < 4 * (4 * r) := by sorry
