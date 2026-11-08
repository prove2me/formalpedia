-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_originalBoundary_incidenceRelation_eq
-- name    : QEC.Coding.FiberBundle.RandomBase.originalBoundary_incidenceRelation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:23:58.600566+00:00
-- url     : https://prove2.me/theorems/929f30cf-f418-4664-b1e8-dd9e3f1939c5
-- title:
--   Random Base: original Boundary incidence Relation eq
-- statement:
--   The relation-defined original Tanner boundary is exactly the sampled
--   binary boundary matrix, not an externally supplied representation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L22-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L22-L39

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.originalBoundary_incidenceRelation_eq
    {r : Nat} (sample : Sample r) :
    ClassicalWeightReduction.originalBoundary (F := ZMod 2)
        (incidenceRelation sample) =
      Matrix.toLin' (boundary sample) := by sorry
