-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productCore_of_residualRankOne_for_D5
-- name    : QEC.Bounds.BPTCommutingProjectorModel.productCore_of_residualRankOne_for_D5
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-17T23:26:32.437928+00:00
-- url     : https://prove2.me/theorems/993524e2-5920-4704-84ea-1de06a8dfa12
-- title:
--   BPTCommuting Projector Model: product Core of residual Rank One for D5
-- statement:
--   Convert the fixed-data rank-one residual factor into the exact product block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/ProductCore.lean#L33-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/ProductCore.lean#L33-L103

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCoreData
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductFactorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1800000

theorem QEC.Bounds.BPTCommutingProjectorModel.productCore_of_residualRankOne_for_D5
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Pfirst : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (WC.restrictScalars Complex)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hresidual : M.FixedActiveDataResidualRankOne
      region bcomponent ccomponent WB WC UB UC Pfirst P_D Qsecond) :
    M.FixedActiveDataProductCore
      region bcomponent ccomponent WB WC UB UC P_D Qsecond := by sorry
