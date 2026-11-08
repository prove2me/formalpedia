-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_r_le_finrank_ker_boundary2
-- name    : QEC.Coding.FiberBundle.r_le_finrank_ker_boundary2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:00:34.547031+00:00
-- url     : https://prove2.me/theorems/83dfd044-f947-4410-9dd6-248b04808d10
-- title:
--   Fiber Bundle: r le finrank ker boundary2
-- statement:
--   The kernel of the second bundle boundary contains an `r`-dimensional
--   constant-fiber sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/HomologyDimension.lean#L89-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/HomologyDimension.lean#L89-L110

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle

theorem QEC.Coding.FiberBundle.r_le_finrank_ker_boundary2
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    r ≤ Module.finrank (ZMod 2)
      (LinearMap.ker
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample))) := by sorry
