-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_neighborEdgeCount_mono_source
-- name    : QEC.Coding.FiberBundle.TwistGraph.neighborEdgeCount_mono_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:13.721471+00:00
-- url     : https://prove2.me/theorems/1ed9b305-aa61-44e3-b29b-eeba3494b65c
-- title:
--   Twist Graph: neighbor Edge Count mono source
-- statement:
--   Edge count is monotone in its source set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L241-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L241-L249

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.neighborEdgeCount_mono_source
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (source₁ source₂ target : Finset (ZMod ell))
    (hsubset : source₁ ⊆ source₂) :
    neighborEdgeCount twistSample source₁ target ≤
      neighborEdgeCount twistSample source₂ target := by sorry
