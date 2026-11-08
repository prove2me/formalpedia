-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupport_hasNoIsolatedVertices_of_isFullyGood
-- name    : QEC.Coding.FiberBundle.RandomBase.baseSupport_hasNoIsolatedVertices_of_isFullyGood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:09:24.021877+00:00
-- url     : https://prove2.me/theorems/ba14228c-52d9-44d2-8a57-586cab1543b7
-- title:
--   Random Base: base Support has No Isolated Vertices of is Fully Good
-- statement:
--   The concrete random fiber-bundle data therefore satisfies the exact
--   non-isolation premise of its own support-relation reduction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5600-L5619
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5600-L5619

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.baseSupport_hasNoIsolatedVertices_of_isFullyGood
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) baseSample) :
    ClassicalWeightReduction.HasNoIsolatedVertices
      (baseSupportRelation
        (RandomTwist.fiberBundleData baseSample twistSample)) := by sorry
