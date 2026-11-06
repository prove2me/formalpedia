-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hammingWeight_eq_sum_layerWord
-- name    : QEC.Coding.FiberBundle.TwistGraph.hammingWeight_eq_sum_layerWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:46:49.880899+00:00
-- url     : https://prove2.me/theorems/259b8a2e-dac7-44d2-b732-4c76e602e0cc
-- title:
--   Twist Graph: hamming Weight eq sum layer Word
-- statement:
--   Total twist-word weight is the sum of its layer weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L492-L503
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L492-L503

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.hammingWeight_eq_sum_layerWord
    {r ell : Nat}
    [NeZero ell]
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    HammingWeight w =
      ∑ u : ZMod ell, HammingWeight (layerWord w u) := by sorry
