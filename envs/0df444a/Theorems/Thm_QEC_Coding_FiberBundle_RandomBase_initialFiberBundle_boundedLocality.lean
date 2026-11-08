-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_initialFiberBundle_boundedLocality
-- name    : QEC.Coding.FiberBundle.RandomBase.initialFiberBundle_boundedLocality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:40:54.920858+00:00
-- url     : https://prove2.me/theorems/a4e4127f-9a09-43cb-95be-6f9eea864699
-- title:
--   Random Base: initial Fiber Bundle bounded Locality
-- statement:
--   The initial HHO20 fiber-bundle code has locality at most the common
--   Tanner degree-window bound plus the two incident cycle edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/InitialLocality.lean#L59-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/InitialLocality.lean#L59-L135

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open QEC.Coding
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.initialFiberBundle_boundedLocality
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDegree : HasDegreeWindows (Delta := Delta) baseSample) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplex
          (RandomTwist.fiberBundleData
            baseSample twistSample))).localityProfile
      (101 * Delta + 2) := by sorry
