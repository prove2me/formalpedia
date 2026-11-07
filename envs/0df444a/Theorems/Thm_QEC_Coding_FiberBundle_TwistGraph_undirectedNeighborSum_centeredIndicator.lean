-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_undirectedNeighborSum_centeredIndicator
-- name    : QEC.Coding.FiberBundle.TwistGraph.undirectedNeighborSum_centeredIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:17.47707+00:00
-- url     : https://prove2.me/theorems/9241112b-dbd0-4060-839c-ad0f6421f7d5
-- title:
--   Twist Graph: undirected Neighbor Sum centered Indicator
-- statement:
--   Centering a target indicator turns its neighbor sum into discrepancy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L186-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L186-L205

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.undirectedNeighborSum_centeredIndicator
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (vertices : Finset (ZMod ell))
    (u : ZMod ell) :
    undirectedNeighborSum twistSample (centeredIndicator vertices) u =
      ell * neighborIncidenceCount twistSample vertices u -
        2 * typeCount * vertices.card := by sorry
