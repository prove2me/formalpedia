-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_heavy_light_discrepancy_bound
-- name    : QEC.Coding.FiberBundle.TwistGraph.heavy_light_discrepancy_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:48:29.255194+00:00
-- url     : https://prove2.me/theorems/b22aa34b-9b57-478d-816d-48a43f247156
-- title:
--   Twist Graph: heavy light discrepancy bound
-- statement:
--   In the heavy case, the variance term for `(H,L)` is at most
--   `sqrt(1001) * ell * |H| < 32 * ell * |H|`; after including degree `2k`,
--   the cleared discrepancy is bounded by `64 * k * ell * |H|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectral.lean#L107-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectral.lean#L107-L170

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Mathlib.Data.Nat.Dist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.heavy_light_discrepancy_bound
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hSquared : HasHHO20SquaredExpanderMixing twistSample)
    (hcase :
      (mediumLayerSet Delta w).card <
        1000 * (heavyLayerSet Delta w).card) :
    50000 *
        Nat.dist
          (ell *
            neighborEdgeCount twistSample
              (heavyLayerSet Delta w) (lightLayerSet Delta w))
          (2 * typeCount *
            (heavyLayerSet Delta w).card *
            (lightLayerSet Delta w).card) ≤
      64 * typeCount * ell * (heavyLayerSet Delta w).card := by sorry
