-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_snd_mem_horizontalBoundaryShadow_of_mem_twistGraph_violationSet
-- name    : QEC.Coding.FiberBundle.snd_mem_horizontalBoundaryShadow_of_mem_twistGraph_violationSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:22.7892+00:00
-- url     : https://prove2.me/theorems/09ba0263-cec1-4a1c-beda-e3eae33a2260
-- title:
--   Fiber Bundle: snd mem horizontal Boundary Shadow of mem twist Graph violation Set
-- statement:
--   Every violated twist-graph check projects to a nonzero bundle boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2246-L2267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2246-L2267

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.snd_mem_horizontalBoundaryShadow_of_mem_twistGraph_violationSet
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (ua : ZMod ell × Fin (3 * r))
    (hua :
      ua ∈ TwistGraph.violationSet baseSample twistSample
        (twistGraphWordOfHorizontalComponent z)) :
    ua.2 ∈ horizontalBoundaryShadow baseSample twistSample
      (horizontalComponent z) := by sorry
