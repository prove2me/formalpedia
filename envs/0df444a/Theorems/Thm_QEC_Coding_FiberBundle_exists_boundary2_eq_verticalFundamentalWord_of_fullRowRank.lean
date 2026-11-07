-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_boundary2_eq_verticalFundamentalWord_of_fullRowRank
-- name    : QEC.Coding.FiberBundle.exists_boundary2_eq_verticalFundamentalWord_of_fullRowRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:49:21.790296+00:00
-- url     : https://prove2.me/theorems/8f1c4b87-2427-4d49-939e-ac75175dbd8c
-- title:
--   Fiber Bundle: exists boundary2 eq vertical Fundamental Word of full Row Rank
-- statement:
--   Full row rank supplies the constant-fiber two-chain whose boundary realizes
--   any prescribed collection of vertical fundamental cycles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L619-L638
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L619-L638

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_boundary2_eq_verticalFundamentalWord_of_fullRowRank
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (y : Word (ZMod 2) (Fin (3 * r))) :
    ∃ c : Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell))),
      boundary2
          (RandomTwist.fiberBundleData baseSample twistSample) c =
        verticalFundamentalWord
          (baseOne := Fin (4 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) y := by sorry
