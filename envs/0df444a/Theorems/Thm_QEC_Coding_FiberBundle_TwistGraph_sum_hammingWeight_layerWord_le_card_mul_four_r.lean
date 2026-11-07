-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_hammingWeight_layerWord_le_card_mul_four_r
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_hammingWeight_layerWord_le_card_mul_four_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:28.205203+00:00
-- url     : https://prove2.me/theorems/252d5b0f-3b7b-4fe7-8d87-c0e9dfb28975
-- title:
--   Twist Graph: sum hamming Weight layer Word le card mul four r
-- statement:
--   Sum of layer weights over a set is at most `n` times its cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L895-L907
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L895-L907

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_hammingWeight_layerWord_le_card_mul_four_r
    {r ell : Nat}
    [NeZero ell]
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (layers : Finset (ZMod ell)) :
    (∑ u ∈ layers, HammingWeight (layerWord w u)) ≤
      layers.card * (4 * r) := by sorry
