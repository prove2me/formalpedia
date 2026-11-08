-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupportRelation_randomFiberBundleData_iff
-- name    : QEC.Coding.FiberBundle.RandomBase.baseSupportRelation_randomFiberBundleData_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:05:35.266183+00:00
-- url     : https://prove2.me/theorems/c20b3d9a-d747-42a5-bc25-89e93243cc4b
-- title:
--   Random Base: base Support Relation random Fiber Bundle Data iff
-- statement:
--   The Random Base construction uses the base Support Relation random Fiber Bundle Data iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5586-L5596
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5586-L5596

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.baseSupportRelation_randomFiberBundleData_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (a : Fin (3 * r)) (b : Fin (4 * r)) :
    baseSupportRelation
        (RandomTwist.fiberBundleData baseSample twistSample) a b ↔
      incidenceRelation baseSample a b := by sorry
