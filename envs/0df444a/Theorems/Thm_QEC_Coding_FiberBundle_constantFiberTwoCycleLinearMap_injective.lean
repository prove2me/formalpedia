-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_constantFiberTwoCycleLinearMap_injective
-- name    : QEC.Coding.FiberBundle.constantFiberTwoCycleLinearMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:59:54.482317+00:00
-- url     : https://prove2.me/theorems/fc67378e-3268-4a6a-bb6f-6c176c6fd199
-- title:
--   Fiber Bundle: constant Fiber Two Cycle Linear Map injective
-- statement:
--   The constant-fiber two-cycle embedding remembers the base codeword.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/HomologyDimension.lean#L73-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/HomologyDimension.lean#L73-L85

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle

theorem QEC.Coding.FiberBundle.constantFiberTwoCycleLinearMap_injective
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Function.Injective
      (constantFiberTwoCycleLinearMap baseSample twistSample) := by sorry
