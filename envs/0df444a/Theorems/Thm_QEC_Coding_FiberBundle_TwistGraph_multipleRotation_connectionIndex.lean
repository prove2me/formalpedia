-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_multipleRotation_connectionIndex
-- name    : QEC.Coding.FiberBundle.TwistGraph.multipleRotation_connectionIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:43:09.580507+00:00
-- url     : https://prove2.me/theorems/d9a914ae-e4ef-4a3f-b5ea-8bd69e9716bf
-- title:
--   Twist Graph: multiple Rotation connection Index
-- statement:
--   Every incidence connection is either the identity (a head) or the embedded
--   nonzero step of its check type (a tail).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L258-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L258-L274

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.multipleRotation_connectionIndex
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (sample : RandomTwist.Sample r typeCount ell)
    (b : Fin (4 * r)) (a : Fin (3 * r)) :
    multipleRotation ell (RandomTwist.connectionIndex sample b a) =
      if RandomTwist.isTail sample a b then
        layerEmbedding ell
          (step sample (RandomTwist.checkType typeCount a))
      else
        0 := by sorry
