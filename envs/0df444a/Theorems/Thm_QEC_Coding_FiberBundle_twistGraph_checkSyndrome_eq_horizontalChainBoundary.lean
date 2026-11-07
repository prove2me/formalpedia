-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_twistGraph_checkSyndrome_eq_horizontalChainBoundary
-- name    : QEC.Coding.FiberBundle.twistGraph_checkSyndrome_eq_horizontalChainBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:37.349469+00:00
-- url     : https://prove2.me/theorems/7cbea4c9-5353-4393-964e-11c1d163182f
-- title:
--   Fiber Bundle: twist Graph check Syndrome eq horizontal Chain Boundary
-- statement:
--   The parity check on the type edge out of `u` is exactly the horizontal bundle
--   boundary at the embedded target layer.  This fixes the source/target
--   orientation used by the later LTC argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2206-L2229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2206-L2229

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.twistGraph_checkSyndrome_eq_horizontalChainBoundary
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (u : ZMod ell) (a : Fin (3 * r)) :
    TwistGraph.checkSyndrome baseSample twistSample
        (twistGraphWordOfHorizontalComponent z) u a =
      horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a
        (TwistGraph.layerEmbedding ell
          (TwistGraph.outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u)) := by sorry
