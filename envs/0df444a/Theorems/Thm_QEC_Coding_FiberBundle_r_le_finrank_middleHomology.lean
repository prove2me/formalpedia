-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_r_le_finrank_middleHomology
-- name    : QEC.Coding.FiberBundle.r_le_finrank_middleHomology
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:02:29.555609+00:00
-- url     : https://prove2.me/theorems/ef7da567-ebf9-4b4a-a884-c56442e0e2d1
-- title:
--   Fiber Bundle: r le finrank middle Homology
-- statement:
--   The initial HHO20 fiber bundle encodes at least `r` logical qubits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/HomologyDimension.lean#L113-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/HomologyDimension.lean#L113-L189

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle

theorem QEC.Coding.FiberBundle.r_le_finrank_middleHomology
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    r ≤ Module.finrank (ZMod 2)
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleHomology := by sorry
