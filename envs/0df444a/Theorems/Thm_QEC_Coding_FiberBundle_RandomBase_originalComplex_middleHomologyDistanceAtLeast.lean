-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_originalComplex_middleHomologyDistanceAtLeast
-- name    : QEC.Coding.FiberBundle.RandomBase.originalComplex_middleHomologyDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:31:25.496523+00:00
-- url     : https://prove2.me/theorems/557a983c-47af-4395-ad78-2c7463f9e69e
-- title:
--   Random Base: original Complex middle Homology Distance At Least
-- statement:
--   The original Tanner complex inherits the explicit `4r/5` distance from
--   the fully-good random-base event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L92-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L92-L114

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.originalComplex_middleHomologyDistanceAtLeast
    {r Delta : Nat} (sample : Sample r)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    MiddleHomologyDistanceAtLeast
      (ClassicalWeightReduction.originalComplex (F₀ := ZMod 2)
        (incidenceRelation sample))
      ((4 * r) / 5) := by sorry
