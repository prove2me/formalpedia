-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_eq_of_add_mem_middleBoundaryCode
-- name    : QEC.Coding.FiberBundle.homologyBaseProjection_eq_of_add_mem_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:54:07.394842+00:00
-- url     : https://prove2.me/theorems/d20aa8d4-efaa-42a9-9740-4d0d4dbca7dd
-- title:
--   Fiber Bundle: homology Base Projection eq of add mem middle Boundary Code
-- statement:
--   Homologous bundle words have the same bundle-to-base homology projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4229-L4256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4229-L4256

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.homologyBaseProjection_eq_of_add_mem_middleBoundaryCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z' z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hHomologous :
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier) :
    homologyBaseProjection z' = homologyBaseProjection z := by sorry
