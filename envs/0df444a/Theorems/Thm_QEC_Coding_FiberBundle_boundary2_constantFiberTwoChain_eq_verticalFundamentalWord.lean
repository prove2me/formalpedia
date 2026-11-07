-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_boundary2_constantFiberTwoChain_eq_verticalFundamentalWord
-- name    : QEC.Coding.FiberBundle.boundary2_constantFiberTwoChain_eq_verticalFundamentalWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:49:07.881188+00:00
-- url     : https://prove2.me/theorems/e04795a7-3a8c-481a-b6ad-b333661020ee
-- title:
--   Fiber Bundle: boundary2 constant Fiber Two Chain eq vertical Fundamental Word
-- statement:
--   The boundary of a constant-fiber two-chain is the pure vertical fundamental
--   word whose coefficient vector is the ordinary sampled base boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L574-L613
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L574-L613

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.boundary2_constantFiberTwoChain_eq_verticalFundamentalWord
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r))) :
    boundary2
        (RandomTwist.fiberBundleData baseSample twistSample)
        (constantFiberTwoChain
          (fiberOne := ZMod (ell * ell)) x) =
      verticalFundamentalWord
        (baseOne := Fin (4 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell))
        (Matrix.toLin' (RandomBase.boundary baseSample) x) := by sorry
