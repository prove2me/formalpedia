-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyOutputEmbedding_eq_compressionCoordinateEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_compressionCoordinateEmbedding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T05:06:54.336835+00:00
-- url     : https://prove2.me/theorems/be365935-b951-4fdc-bed3-32cf9c3e769c
-- title:
--   BPTCommuting Projector Model: final Assembly Output Embedding eq compression Coordinate Embedding
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Output Embedding eq compression Coordinate Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/CompressionExteriorCoordinates.lean#L136-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/CompressionExteriorCoordinates.lean#L136-L162

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorCoordinates
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

theorem QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_compressionCoordinateEmbedding
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
        (isotypicLiftedMultiplicity.{0} nC))) :
    M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC =
      (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        (M.finalAssemblyCompressionCoordinateEmbedding
          region bcomponent ccomponent WB WC UB UC) := by sorry
