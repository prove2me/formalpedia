-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_lightLayerSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_lightLayerSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:43:36.850422+00:00
-- url     : https://prove2.me/theorems/0e266297-648e-4167-9737-052fef21d679
-- title:
--   Twist Graph: mem light Layer Set iff
-- statement:
--   The Twist Graph construction uses the mem light Layer Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L318-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L318-L327

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_lightLayerSet_iff
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ lightLayerSet Delta w ↔
      Delta * HammingWeight (layerWord w u) ≤ 2 * (4 * r) := by sorry
