-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyInputEmbedding_eq_outputEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_outputEmbedding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T04:12:46.794193+00:00
-- url     : https://prove2.me/theorems/b5fa8106-dc9e-4d3b-b2fc-97290353f69f
-- title:
--   BPTCommuting Projector Model: final Assembly Input Embedding eq output Embedding
-- statement:
--   The two named final-assembly embeddings are the same coordinate map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L219-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L219-L242

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
set_option maxHeartbeats 1600000

theorem QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_outputEmbedding
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
    M.finalAssemblyInputEmbedding region bcomponent ccomponent WB WC UB UC =
      M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC := by sorry
