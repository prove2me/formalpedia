-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
-- name    : QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:42:35.473246+00:00
-- url     : https://prove2.me/theorems/744c86d4-2b63-438f-b564-77f20434089d
-- title:
--   Fiber Bundle: mem horizontal Boundary Shadow iff
-- statement:
--   The Fiber Bundle construction uses the mem horizontal Boundary Shadow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2232-L2243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2232-L2243

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) :
    a ∈ horizontalBoundaryShadow baseSample twistSample h ↔
      ∃ j, horizontalChainBoundary baseSample twistSample h a j ≠ 0 := by sorry
