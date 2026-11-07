-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_mem_middleBoundaryCode_iff_of_add_mem
-- name    : QEC.Coding.FiberBundle.mem_middleBoundaryCode_iff_of_add_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:54:11.232273+00:00
-- url     : https://prove2.me/theorems/df58e152-8279-4688-adbd-aa847302df2d
-- title:
--   Fiber Bundle: mem middle Boundary Code iff of add mem
-- statement:
--   Homologous bundle words are boundaries simultaneously.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4259-L4315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4259-L4315

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.mem_middleBoundaryCode_iff_of_add_mem
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
    z' ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by sorry
