-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_finrank_weightReducedClassicalKernel_eq
-- name    : QEC.Coding.FiberBundle.RandomBase.finrank_weightReducedClassicalKernel_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:46.846861+00:00
-- url     : https://prove2.me/theorems/43fd55eb-4d05-417f-a51b-d1dbe1e68c35
-- title:
--   Random Base: finrank weight Reduced Classical Kernel eq
-- statement:
--   The internally extracted classical parity-check matrix has kernel
--   dimension exactly `r`; no rank certificate is supplied by a caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L172-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L172-L201

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.finrank_weightReducedClassicalKernel_eq
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Module.finrank (ZMod 2)
        (LinearMap.ker (Matrix.toLin'
          (LinearMap.toMatrix'
            (ClassicalWeightReduction.boundary (F := ZMod 2)
              (incidenceRelation sample))))) = r := by sorry
