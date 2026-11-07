-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_connection_onOne
-- name    : QEC.Coding.FiberBundle.fiberResidue_connection_onOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:50:00.730213+00:00
-- url     : https://prove2.me/theorems/0161088d-637c-49a5-bbd0-537f6bafd146
-- title:
--   Fiber Bundle: fiber Residue connection on One
-- statement:
--   The one-cell action of every construction connection preserves residue too.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L956-L972
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L956-L972

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.fiberResidue_connection_onOne
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b : Fin (4 * r)) (a : Fin (3 * r))
    (j : ZMod (ell * ell)) :
    fiberResidue ell
        ((((RandomTwist.fiberBundleData baseSample twistSample
          ).connection b a).onOne) j) =
      fiberResidue ell j := by sorry
