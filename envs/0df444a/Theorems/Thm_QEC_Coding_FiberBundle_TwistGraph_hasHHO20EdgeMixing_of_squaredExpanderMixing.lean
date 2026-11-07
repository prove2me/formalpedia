-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hasHHO20EdgeMixing_of_squaredExpanderMixing
-- name    : QEC.Coding.FiberBundle.TwistGraph.hasHHO20EdgeMixing_of_squaredExpanderMixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:48:35.460379+00:00
-- url     : https://prove2.me/theorems/1504b47b-5187-4a16-ae27-171910b5456f
-- title:
--   Twist Graph: has HHO20 Edge Mixing of squared Expander Mixing
-- statement:
--   Squared expander mixing implies the two numerical edge estimates used by the
--   deterministic HHO20 proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectral.lean#L176-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectral.lean#L176-L274

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Mathlib.Data.Nat.Dist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.hasHHO20EdgeMixing_of_squaredExpanderMixing
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hSquared : HasHHO20SquaredExpanderMixing twistSample) :
    HasHHO20EdgeMixing Delta twistSample := by sorry
