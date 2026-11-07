-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_not_mem_middleBoundaryCode_iff_projection_ne_zero
-- name    : QEC.Coding.FiberBundle.not_mem_middleBoundaryCode_iff_projection_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:49:38.021586+00:00
-- url     : https://prove2.me/theorems/27023b4c-844e-4c44-a3d2-3d810db7d9f0
-- title:
--   Fiber Bundle: not mem middle Boundary Code iff projection ne zero
-- statement:
--   For bundle cycles over a full-row-rank base, nontrivial first homology is
--   equivalent to nonzero base projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L742-L765
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L742-L765

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.not_mem_middleBoundaryCode_iff_projection_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier) :
    z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleBoundaryCode.carrier ↔
      homologyBaseProjection z ≠ 0 := by sorry
