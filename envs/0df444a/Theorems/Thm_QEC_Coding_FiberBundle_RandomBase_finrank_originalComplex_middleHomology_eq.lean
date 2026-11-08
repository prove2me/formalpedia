-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_finrank_originalComplex_middleHomology_eq
-- name    : QEC.Coding.FiberBundle.RandomBase.finrank_originalComplex_middleHomology_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:32.074948+00:00
-- url     : https://prove2.me/theorems/e2313b23-da5d-4fad-bdbf-b0d490069749
-- title:
--   Random Base: finrank original Complex middle Homology eq
-- statement:
--   The original sampled Tanner complex has exactly the advertised `r`
--   logical dimensions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L118-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L118-L145

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.finrank_originalComplex_middleHomology_eq
    {r Delta : Nat} (sample : Sample r)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Module.finrank (ZMod 2)
        (ClassicalWeightReduction.originalComplex (F₀ := ZMod 2)
          (incidenceRelation sample)).middleHomology = r := by sorry
