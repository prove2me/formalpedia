-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hammingWeight_eq_nonheavy_add_heavy
-- name    : QEC.Coding.FiberBundle.TwistGraph.hammingWeight_eq_nonheavy_add_heavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:05.302404+00:00
-- url     : https://prove2.me/theorems/6ded6b3f-074b-4733-9321-429fb2b703ef
-- title:
--   Twist Graph: hamming Weight eq nonheavy add heavy
-- statement:
--   Total word weight splits exactly across nonheavy and heavy layers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L910-L923
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L910-L923

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.hammingWeight_eq_nonheavy_add_heavy
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    HammingWeight w =
      (∑ u ∈ nonheavyLayerSet Delta w,
        HammingWeight (layerWord w u)) +
      (∑ u ∈ heavyLayerSet Delta w,
        HammingWeight (layerWord w u)) := by sorry
