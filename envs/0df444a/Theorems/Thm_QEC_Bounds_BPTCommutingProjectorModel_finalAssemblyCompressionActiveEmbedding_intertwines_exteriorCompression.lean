-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyCompressionActiveEmbedding_intertwines_exteriorCompression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyCompressionActiveEmbedding_intertwines_exteriorCompression
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T05:38:10.132817+00:00
-- url     : https://prove2.me/theorems/ff5df691-f599-4532-9f70-c596da9137e3
-- title:
--   BPTCommuting Projector Model: final Assembly Compression Active Embedding intertwines exterior Compression
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Compression Active Embedding intertwines exterior Compression property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IntertwiningTensor.lean#L33-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IntertwiningTensor.lean#L33-L79

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningComplement
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorActiveStatement
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningTensor
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
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000

theorem QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyCompressionActiveEmbedding_intertwines_exteriorCompression
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
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let S := M.regionSubsystem region
    let J := M.finalAssemblyCompressionActiveEmbedding
      region bcomponent ccomponent WB WC UB UC
    (TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
        (M.exteriorCompressionComplementAction region P)).comp J =
      J.comp (M.finalAssemblyCompressionActiveResult region nB nC WB WC
        (M.exteriorCompressionWitness region P)) := by sorry
