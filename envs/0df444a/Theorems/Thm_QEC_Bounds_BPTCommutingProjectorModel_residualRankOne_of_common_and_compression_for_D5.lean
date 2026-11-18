-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_residualRankOne_of_common_and_compression_for_D5
-- name    : QEC.Bounds.BPTCommutingProjectorModel.residualRankOne_of_common_and_compression_for_D5
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-17T22:29:49.691376+00:00
-- url     : https://prove2.me/theorems/a3cbdf75-5c18-4d0b-bafd-ce801f0cd02a
-- title:
--   BPTCommuting Projector Model: residual Rank One of common and compression for D5
-- statement:
--   The BPTCommuting Projector Model construction uses the residual Rank One of common and compression for D5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/RankOne.lean#L32-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/RankOne.lean#L32-L113

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Compression
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_RankOne
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

theorem QEC.Bounds.BPTCommutingProjectorModel.residualRankOne_of_common_and_compression_for_D5
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
    (hcommonData : M.FixedActiveCommonFactorizationData
      region bcomponent ccomponent WB WC UB UC Pfirst P_D Qsecond)
    (hcompressionData : M.FixedActiveRegroupedCompressionData
      region ccomponent WC UC Qsecond) :
    M.FixedActiveDataResidualRankOne
      region bcomponent ccomponent WB WC UB UC Pfirst P_D Qsecond := by sorry
