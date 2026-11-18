-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyCompressionActiveEmbedding_adjoint_comp_self
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyCompressionActiveEmbedding_adjoint_comp_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T05:26:53.795883+00:00
-- url     : https://prove2.me/theorems/afff3702-c65b-4f3a-b953-929e0c31a951
-- title:
--   BPTCommuting Projector Model: final Assembly Compression Active Embedding adjoint comp self
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Compression Active Embedding adjoint comp self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IsometryActive.lean#L31-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IsometryActive.lean#L31-L64

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryStatement
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryActive
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 180000

theorem QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyCompressionActiveEmbedding_adjoint_comp_self
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
    let J := M.finalAssemblyCompressionActiveEmbedding
      region bcomponent ccomponent WB WC UB UC
    (LinearMap.adjoint J).comp J =
      (1 : Semantics.Operator (M.FinalAssemblyCompressionDomain region nB nC WB WC)) := by sorry
