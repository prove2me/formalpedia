-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_range_finrank_le_one_of_region_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_range_finrank_le_one_of_region_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:49:41.134127+00:00
-- url     : https://prove2.me/theorems/0af47589-261d-4d01-9ebf-4d99757ebe80
-- title:
--   BPTCommuting Projector Model: second Cut Pleft range finrank le one of region recoverable
-- statement:
--   The hM scalar-compression bridge forces the selected source `Pi_AB'` factor
--   to have at most one-dimensional range.  This is the finite-dimensional
--   rank-one step at BPT source lines 643--647.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOne.lean#L30-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOne.lean#L30-L67

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOne
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOne
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1600000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_range_finrank_le_one_of_region_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region →
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      Module.finrank Complex (LinearMap.range Pleft) ≤ 1 := by sorry
