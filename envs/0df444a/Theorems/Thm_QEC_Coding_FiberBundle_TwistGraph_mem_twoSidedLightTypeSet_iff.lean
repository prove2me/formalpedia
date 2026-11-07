-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_twoSidedLightTypeSet_iff
-- name    : QEC.Coding.FiberBundle.TwistGraph.mem_twoSidedLightTypeSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:44:39.382814+00:00
-- url     : https://prove2.me/theorems/bed86f0e-b919-4ebc-bb3d-4aff048dea9d
-- title:
--   Twist Graph: mem two Sided Light Type Set iff
-- statement:
--   The Twist Graph construction uses the mem two Sided Light Type Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L505-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L505-L516

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.mem_twoSidedLightTypeSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) :
    τ ∈ twoSidedLightTypeSet Delta twistSample w u ↔
      outNeighbor twistSample τ u ∈ lightLayerSet Delta w ∧
        inNeighbor twistSample τ u ∈ lightLayerSet Delta w := by sorry
