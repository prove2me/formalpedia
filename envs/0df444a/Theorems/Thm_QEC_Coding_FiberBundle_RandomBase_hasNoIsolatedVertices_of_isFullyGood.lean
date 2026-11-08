-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_hasNoIsolatedVertices_of_isFullyGood
-- name    : QEC.Coding.FiberBundle.RandomBase.hasNoIsolatedVertices_of_isFullyGood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:05:47.49196+00:00
-- url     : https://prove2.me/theorems/9f7d63bb-6bec-4ad6-b45f-df373e30f620
-- title:
--   Random Base: has No Isolated Vertices of is Fully Good
-- statement:
--   Every fully-good HHO20 sample supplies the local hypotheses required by
--   classical weight reduction; callers do not provide them separately.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5577-L5583
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5577-L5583

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.hasNoIsolatedVertices_of_isFullyGood
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    ClassicalWeightReduction.HasNoIsolatedVertices
      (incidenceRelation sample) := by sorry
