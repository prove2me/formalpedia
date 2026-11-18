-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeComplementEmbeddingCore_intertwines_exteriorCompression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbeddingCore_intertwines_exteriorCompression
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T05:22:28.621611+00:00
-- url     : https://prove2.me/theorems/2467b18b-cca1-4ac3-9005-c02dd4277824
-- title:
--   BPTCommuting Projector Model: active Complement Embedding Core intertwines exterior Compression
-- statement:
--   The BPTCommuting Projector Model construction uses the active Complement Embedding Core intertwines exterior Compression property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IntertwiningComplement.lean#L31-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IntertwiningComplement.lean#L31-L87

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningStatement
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ComplementIntertwiningCore
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningComplement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

theorem QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbeddingCore_intertwines_exteriorCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    let eComp := M.activeComplementEmbeddingCore region ccomponent WC UC
    let Dcomp : Semantics.Operator (ActiveComplementDomain M region nC WC) :=
      TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
        (TensorProduct.map
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
          (M.exteriorCompressionWitness region P))
    (M.exteriorCompressionComplementAction region P).comp eComp.toLinearMap =
      eComp.toLinearMap.comp Dcomp := by sorry
