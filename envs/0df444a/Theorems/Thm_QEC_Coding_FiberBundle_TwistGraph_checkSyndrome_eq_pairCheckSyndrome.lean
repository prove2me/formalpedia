-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_checkSyndrome_eq_pairCheckSyndrome
-- name    : QEC.Coding.FiberBundle.TwistGraph.checkSyndrome_eq_pairCheckSyndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:00.734308+00:00
-- url     : https://prove2.me/theorems/233ea8dd-a490-4532-823c-2124dfb6e68a
-- title:
--   Twist Graph: check Syndrome eq pair Check Syndrome
-- statement:
--   A graph check is definitionally the corresponding type check on its source
--   and target layer words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L88-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L88-L102

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.checkSyndrome_eq_pairCheckSyndrome
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (a : Fin (3 * r)) :
    checkSyndrome baseSample twistSample w u a =
      pairCheckSyndrome baseSample twistSample
        (layerWord w u)
        (layerWord w
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u))
        a := by sorry
