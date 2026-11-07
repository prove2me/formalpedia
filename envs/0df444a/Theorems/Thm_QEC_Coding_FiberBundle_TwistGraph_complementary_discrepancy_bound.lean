-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_complementary_discrepancy_bound
-- name    : QEC.Coding.FiberBundle.TwistGraph.complementary_discrepancy_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:48:03.982528+00:00
-- url     : https://prove2.me/theorems/f60a7864-f67d-4be1-9fdd-9f8f7de3a89e
-- title:
--   Twist Graph: complementary discrepancy bound
-- statement:
--   For complementary nonheavy/heavy sets, the square-root variance term is
--   exactly `|nonheavy| * |heavy|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectral.lean#L48-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectral.lean#L48-L100

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Mathlib.Data.Nat.Dist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.complementary_discrepancy_bound
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hSquared : HasHHO20SquaredExpanderMixing twistSample) :
    50000 *
        Nat.dist
          (ell *
            neighborEdgeCount twistSample
              (nonheavyLayerSet Delta w) (heavyLayerSet Delta w))
          (2 * typeCount *
            (nonheavyLayerSet Delta w).card *
            (heavyLayerSet Delta w).card) ≤
      2 * typeCount *
        (nonheavyLayerSet Delta w).card *
        (heavyLayerSet Delta w).card := by sorry
