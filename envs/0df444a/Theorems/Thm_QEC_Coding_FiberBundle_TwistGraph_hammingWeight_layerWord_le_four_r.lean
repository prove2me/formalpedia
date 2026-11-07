-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hammingWeight_layerWord_le_four_r
-- name    : QEC.Coding.FiberBundle.TwistGraph.hammingWeight_layerWord_le_four_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:08.321144+00:00
-- url     : https://prove2.me/theorems/1d89adc8-f5ba-48c3-9fd3-b54f0ceb90aa
-- title:
--   Twist Graph: hamming Weight layer Word le four r
-- statement:
--   A layer word has at most `n = 4r` nonzero coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L883-L892
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L883-L892

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.hammingWeight_layerWord_le_four_r
    {r ell : Nat}
    [NeZero ell]
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    HammingWeight (layerWord w u) ≤ 4 * r := by sorry
