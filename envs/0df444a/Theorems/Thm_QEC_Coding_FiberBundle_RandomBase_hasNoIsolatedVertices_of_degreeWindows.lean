-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_hasNoIsolatedVertices_of_degreeWindows
-- name    : QEC.Coding.FiberBundle.RandomBase.hasNoIsolatedVertices_of_degreeWindows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:05:13.945553+00:00
-- url     : https://prove2.me/theorems/71f3eb05-bd2b-4728-8e1d-0fb1f5b7ed78
-- title:
--   Random Base: has No Isolated Vertices of degree Windows
-- statement:
--   Positive HHO20 degree windows exclude every isolated Tanner vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5532-L5546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5532-L5546

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.hasNoIsolatedVertices_of_degreeWindows
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hDegree : HasDegreeWindows (Delta := Delta) sample) :
    ClassicalWeightReduction.HasNoIsolatedVertices
      (incidenceRelation sample) := by sorry
