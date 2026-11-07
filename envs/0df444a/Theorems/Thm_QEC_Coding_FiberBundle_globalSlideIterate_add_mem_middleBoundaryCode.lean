-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_globalSlideIterate_add_mem_middleBoundaryCode
-- name    : QEC.Coding.FiberBundle.globalSlideIterate_add_mem_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:54:40.723836+00:00
-- url     : https://prove2.me/theorems/37438739-c6ea-40fd-b198-a698ab53f485
-- title:
--   Fiber Bundle: global Slide Iterate add mem middle Boundary Code
-- statement:
--   Every global-slide iterate differs from the original cycle by a degree-two
--   boundary, so it is genuinely homologous to the original representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4788-L4831
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4788-L4831

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.globalSlideIterate_add_mem_middleBoundaryCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    ∀ k,
      globalSlideIterate baseSample twistSample z k + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by sorry
