-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_badNonheavy_card_bound_of_upperEdgeMixing
-- name    : QEC.Coding.FiberBundle.TwistGraph.badNonheavy_card_bound_of_upperEdgeMixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:12.347417+00:00
-- url     : https://prove2.me/theorems/e3e55961-ff72-41ec-a124-50157fc172c8
-- title:
--   Twist Graph: bad Nonheavy card bound of upper Edge Mixing
-- statement:
--   The upper oriented-edge mixing estimate implies the paper's
--   `1.25 |H|` unusable-nonheavy bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L324-L395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L324-L395

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.badNonheavy_card_bound_of_upperEdgeMixing
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hUpper :
      10 * ell *
          neighborEdgeCount twistSample
            (nonheavyLayerSet Delta w) (heavyLayerSet Delta w) ≤
        22 * typeCount *
          (nonheavyLayerSet Delta w).card *
          (heavyLayerSet Delta w).card) :
    4 * (badNonheavyLayerSet Delta twistSample w).card ≤
      5 * (heavyLayerSet Delta w).card := by sorry
