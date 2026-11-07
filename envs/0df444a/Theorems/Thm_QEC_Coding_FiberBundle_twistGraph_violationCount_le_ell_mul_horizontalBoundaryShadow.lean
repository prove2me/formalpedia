-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_twistGraph_violationCount_le_ell_mul_horizontalBoundaryShadow
-- name    : QEC.Coding.FiberBundle.twistGraph_violationCount_le_ell_mul_horizontalBoundaryShadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:44.09852+00:00
-- url     : https://prove2.me/theorems/be922b42-19a3-4051-91c0-5148105f0596
-- title:
--   Fiber Bundle: twist Graph violation Count le ell mul horizontal Boundary Shadow
-- statement:
--   There are at most `ell` violated twist checks above each base check in the
--   horizontal boundary shadow.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2273-L2301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2273-L2301

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.twistGraph_violationCount_le_ell_mul_horizontalBoundaryShadow
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    TwistGraph.violationCount baseSample twistSample
        (twistGraphWordOfHorizontalComponent z) ≤
      ell *
        (horizontalBoundaryShadow baseSample twistSample
          (horizontalComponent z)).card := by sorry
