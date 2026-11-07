-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_of_horizontalBoundaryOverlap
-- name    : QEC.Coding.FiberBundle.fiberResidue_eq_of_horizontalBoundaryOverlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:50:09.891102+00:00
-- url     : https://prove2.me/theorems/7abbf297-cfd4-47e6-9dea-d996c6578f94
-- title:
--   Fiber Bundle: fiber Residue eq of horizontal Boundary Overlap
-- statement:
--   Adjacent horizontal cells have the same residue class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1039-L1049
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1039-L1049

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.fiberResidue_eq_of_horizontalBoundaryOverlap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    {x y : Fin (4 * r) × ZMod (ell * ell)}
    (hxy : HorizontalBoundaryOverlap baseSample twistSample x y) :
    fiberResidue ell x.2 = fiberResidue ell y.2 := by sorry
