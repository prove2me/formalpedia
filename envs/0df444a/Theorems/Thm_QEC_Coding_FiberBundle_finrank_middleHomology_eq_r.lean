-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_finrank_middleHomology_eq_r
-- name    : QEC.Coding.FiberBundle.finrank_middleHomology_eq_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:40:23.634446+00:00
-- url     : https://prove2.me/theorems/0642bb52-f893-4271-bb14-2afeac31e87d
-- title:
--   Fiber Bundle: finrank middle Homology eq r
-- statement:
--   Full row rank fixes the initial HHO20 bundle's logical dimension exactly
--   at `r`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/CohomologyDimension.lean#L384-L410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/CohomologyDimension.lean#L384-L410

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.finrank_middleHomology_eq_r
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    Module.finrank (ZMod 2)
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleHomology = r := by sorry
