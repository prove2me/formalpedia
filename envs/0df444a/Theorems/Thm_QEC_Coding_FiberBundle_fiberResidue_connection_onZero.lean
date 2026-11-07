-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_connection_onZero
-- name    : QEC.Coding.FiberBundle.fiberResidue_connection_onZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:49:53.54522+00:00
-- url     : https://prove2.me/theorems/0dec6dba-3163-4813-8a8c-870ffe17534a
-- title:
--   Fiber Bundle: fiber Residue connection on Zero
-- statement:
--   Every actual HHO20 connection preserves the fiber residue class because its
--   rotation is a multiple of `ell`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L937-L953
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L937-L953

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.fiberResidue_connection_onZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b : Fin (4 * r)) (a : Fin (3 * r))
    (i : ZMod (ell * ell)) :
    fiberResidue ell
        ((((RandomTwist.fiberBundleData baseSample twistSample
          ).connection b a).onZero) i) =
      fiberResidue ell i := by sorry
