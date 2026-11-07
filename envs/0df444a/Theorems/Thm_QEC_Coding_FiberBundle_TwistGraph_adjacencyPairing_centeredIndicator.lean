-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_adjacencyPairing_centeredIndicator
-- name    : QEC.Coding.FiberBundle.TwistGraph.adjacencyPairing_centeredIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:38.332892+00:00
-- url     : https://prove2.me/theorems/8c310f77-ee83-4af7-b2c9-6f4fb0f98483
-- title:
--   Twist Graph: adjacency Pairing centered Indicator
-- statement:
--   Exact centered-indicator form of the graph edge discrepancy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L227-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L227-L279

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.adjacencyPairing_centeredIndicator
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (left right : Finset (ZMod ell)) :
    adjacencyPairing twistSample
        (centeredIndicator left) (centeredIndicator right) =
      ell *
        (ell * neighborEdgeCount twistSample left right -
          2 * typeCount * left.card * right.card) := by sorry
