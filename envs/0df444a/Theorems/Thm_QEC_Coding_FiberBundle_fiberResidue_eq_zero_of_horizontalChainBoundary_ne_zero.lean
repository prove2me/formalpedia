-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_zero_of_horizontalChainBoundary_ne_zero
-- name    : QEC.Coding.FiberBundle.fiberResidue_eq_zero_of_horizontalChainBoundary_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:48.106201+00:00
-- url     : https://prove2.me/theorems/1b18c3a0-3799-4cfb-8922-719350e09f2d
-- title:
--   Fiber Bundle: fiber Residue eq zero of horizontal Chain Boundary ne zero
-- statement:
--   The boundary of a residue-normalized horizontal sector is supported only at
--   fiber vertices of residue zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2307-L2345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2307-L2345

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.fiberResidue_eq_zero_of_horizontalChainBoundary_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z)
    (a : Fin (3 * r)) (j : ZMod (ell * ell))
    (hj :
      horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a j ≠ 0) :
    fiberResidue ell j = 0 := by sorry
