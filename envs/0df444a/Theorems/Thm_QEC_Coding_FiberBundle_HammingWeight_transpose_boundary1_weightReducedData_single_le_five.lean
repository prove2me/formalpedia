-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary1_weightReducedData_single_le_five
-- name    : QEC.Coding.FiberBundle.HammingWeight_transpose_boundary1_weightReducedData_single_le_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:20:29.142106+00:00
-- url     : https://prove2.me/theorems/f2fdc5d9-3764-4cde-8dba-68fe893292c8
-- title:
--   Fiber Bundle: Hamming Weight transpose boundary1 weight Reduced Data single le five
-- statement:
--   Every X-check row of a weight-reduced bundle has weight at most five when
--   the fiber boundary has row weight at most two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L561-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L561-L570

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

theorem QEC.Coding.FiberBundle.HammingWeight_transpose_boundary1_weightReducedData_single_le_five
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero)
    (hFiber : HammingWeight (fun j => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 (weightReducedData D))
          (Pi.single (q, i) 1)) ≤ 5 := by sorry
