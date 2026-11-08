-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary2_weightReducedData_canonical_le_five
-- name    : QEC.Coding.FiberBundle.HammingWeight_boundary2_weightReducedData_canonical_le_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:24:25.044646+00:00
-- url     : https://prove2.me/theorems/ff77b63f-d314-4344-9c13-9abea104dd6c
-- title:
--   Fiber Bundle: Hamming Weight boundary2 weight Reduced Data canonical le five
-- statement:
--   Canonical-basis form of the reduced-bundle Z-check bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L605-L622
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L605-L622

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u v
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D

theorem QEC.Coding.FiberBundle.HammingWeight_boundary2_weightReducedData_canonical_le_five
    (b : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne)
    (hFiber : HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (boundary2 (weightReducedData D)
          (canonicalBasisWord (F := ZMod 2) (b, j))) ≤ 5 := by sorry
