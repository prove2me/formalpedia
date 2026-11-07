-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_nonempty_supportedHorizontalCell_of_homologyBaseProjection_ne_zero
-- name    : QEC.Coding.FiberBundle.nonempty_supportedHorizontalCell_of_homologyBaseProjection_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:50:22.736806+00:00
-- url     : https://prove2.me/theorems/8ab005b5-990b-4ccf-9756-468b6fa1d8c9
-- title:
--   Fiber Bundle: nonempty supported Horizontal Cell of homology Base Projection ne zero
-- statement:
--   A nonzero bundle-to-base projection supplies an actual horizontal support cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1259-L1279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1259-L1279

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.nonempty_supportedHorizontalCell_of_homologyBaseProjection_ne_zero
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hProjection : homologyBaseProjection z ≠ 0) :
    Nonempty (SupportedHorizontalCell z) := by sorry
