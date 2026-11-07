-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_of_connected_horizontal_positions
-- name    : QEC.Coding.FiberBundle.fiberResidue_eq_of_connected_horizontal_positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:50:08.047543+00:00
-- url     : https://prove2.me/theorems/09deba97-44af-4d0a-9c67-0c56a3ac327b
-- title:
--   Fiber Bundle: fiber Residue eq of connected horizontal positions
-- statement:
--   Two horizontal cells whose bundle boundaries meet over one base zero-cell
--   have the same residue class.  This is the exact discrete invariant used to
--   form the clusters in HHO20 Lemma `sliding`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L987-L1005
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L987-L1005

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.fiberResidue_eq_of_connected_horizontal_positions
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b b' : Fin (4 * r)) (a : Fin (3 * r))
    (i i' : ZMod (ell * ell))
    (hMeet :
      ((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b a).onZero i =
      ((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b' a).onZero i') :
    fiberResidue ell i = fiberResidue ell i' := by sorry
