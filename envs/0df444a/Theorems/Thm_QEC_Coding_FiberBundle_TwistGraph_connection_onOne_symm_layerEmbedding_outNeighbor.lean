-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_connection_onOne_symm_layerEmbedding_outNeighbor
-- name    : QEC.Coding.FiberBundle.TwistGraph.connection_onOne_symm_layerEmbedding_outNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:45:57.721484+00:00
-- url     : https://prove2.me/theorems/e9229caf-f6a9-4cae-85d1-2d3808dcf36f
-- title:
--   Twist Graph: connection on One symm layer Embedding out Neighbor
-- statement:
--   At the target of a type edge, the inverse bundle connection reads a tail at
--   the source layer and a head at the target layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L352-L390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L352-L390

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.connection_onOne_symm_layerEmbedding_outNeighbor
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : ZMod ell) (b : Fin (4 * r)) (a : Fin (3 * r)) :
    ((((RandomTwist.fiberBundleData baseSample twistSample
      ).connection b a).onOne.symm)
        (layerEmbedding ell
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u))) =
      if RandomTwist.isTail twistSample a b then
        layerEmbedding ell u
      else
        layerEmbedding ell
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u) := by sorry
