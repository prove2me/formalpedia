-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_ell_le_hammingWeight_verticalFiber_of_mem_horizontalBoundaryShadow
-- name    : QEC.Coding.FiberBundle.ell_le_hammingWeight_verticalFiber_of_mem_horizontalBoundaryShadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:07.227516+00:00
-- url     : https://prove2.me/theorems/e0e843f3-f06a-4fde-9e19-85bacf465aa6
-- title:
--   Fiber Bundle: ell le hamming Weight vertical Fiber of mem horizontal Boundary Shadow
-- statement:
--   Every normalized horizontal error forces at least `ell` vertical cells.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2907-L2948
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2907-L2948

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.ell_le_hammingWeight_verticalFiber_of_mem_horizontalBoundaryShadow
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z)
    (a : Fin (3 * r))
    (ha :
      a ∈ horizontalBoundaryShadow baseSample twistSample
        (horizontalComponent z)) :
    ell ≤ HammingWeight (verticalFiber z a) := by sorry
