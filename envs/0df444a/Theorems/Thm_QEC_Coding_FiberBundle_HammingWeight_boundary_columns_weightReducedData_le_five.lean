-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary_columns_weightReducedData_le_five
-- name    : QEC.Coding.FiberBundle.HammingWeight_boundary_columns_weightReducedData_le_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:20:25.201102+00:00
-- url     : https://prove2.me/theorems/d81f428e-7103-4695-96e4-aeea019d51b9
-- title:
--   Fiber Bundle: Hamming Weight boundary columns weight Reduced Data le five
-- statement:
--   Every reduced-bundle qubit participates in at most five checks in total
--   when both fiber-boundary row and column weights are at most two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L626-L656
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L626-L656

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

theorem QEC.Coding.FiberBundle.HammingWeight_boundary_columns_weightReducedData_le_five
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne)
    (hFiberRow : ∀ i : fiberZero,
      HammingWeight (fun j => D.fiberBoundary i j) ≤ 2)
    (hFiberCol : ∀ j : fiberOne,
      HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (boundary1 (weightReducedData D) (reducedQubitBasisWord D q)) +
      HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D q)) ≤ 5 := by sorry
