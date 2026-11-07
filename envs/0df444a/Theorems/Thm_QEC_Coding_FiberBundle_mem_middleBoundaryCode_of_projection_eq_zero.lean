-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_mem_middleBoundaryCode_of_projection_eq_zero
-- name    : QEC.Coding.FiberBundle.mem_middleBoundaryCode_of_projection_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:49:41.186934+00:00
-- url     : https://prove2.me/theorems/61fb1350-2a87-4d18-aa05-d317df931bab
-- title:
--   Fiber Bundle: mem middle Boundary Code of projection eq zero
-- statement:
--   Over a full-row-rank sampled base, every bundle cycle with zero base
--   projection is the boundary of an explicit sum of two two-chains:
--
--   * fiberwise prefix primitives clear its horizontal sector;
--   * a constant-fiber lift supplied by base surjectivity clears the remaining
--     vertical fundamental cycles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L650-L736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L650-L736

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.mem_middleBoundaryCode_of_projection_eq_zero
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
        ).middleCycleCode.carrier)
    (hzProjection : homologyBaseProjection z = 0) :
    z ∈ (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).middleBoundaryCode.carrier := by sorry
