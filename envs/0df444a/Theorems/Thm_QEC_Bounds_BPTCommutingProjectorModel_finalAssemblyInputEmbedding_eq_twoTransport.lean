-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyInputEmbedding_eq_twoTransport
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_twoTransport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T04:13:54.170083+00:00
-- url     : https://prove2.me/theorems/fa480d1f-0b65-4d93-a1dc-a093c6212bcd
-- title:
--   BPTCommuting Projector Model: final Assembly Input Embedding eq two Transport
-- statement:
--   The input embedding in the exact two-transport normal form used by final assembly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L246-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L246-L271

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_twoTransport
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
    (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (TensorProduct.map
            (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap)) =
      M.finalAssemblyInputEmbedding region bcomponent ccomponent WB WC UB UC := by sorry
