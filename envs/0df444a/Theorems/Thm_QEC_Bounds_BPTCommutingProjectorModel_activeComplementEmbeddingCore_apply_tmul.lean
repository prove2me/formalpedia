-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeComplementEmbeddingCore_apply_tmul
-- name    : QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbeddingCore_apply_tmul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T00:02:58.565669+00:00
-- url     : https://prove2.me/theorems/ed06f895-7a7f-4472-a871-ed0cc32fe099
-- title:
--   BPTCommuting Projector Model: active Complement Embedding Core apply tmul
-- statement:
--   The concrete active-complement embedding on a pure tensor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/ComplementEmbeddingCore.lean#L70-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/ComplementEmbeddingCore.lean#L70-L92

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_ComplementEmbeddingCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbeddingCore_apply_tmul
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
    (x : WC.restrictScalars Complex) (n : isotypicLiftedMultiplicity.{0} nC)
    (d : M.fourFactorD region) :
    M.activeComplementEmbeddingCore region ccomponent WC UC
        (x ⊗ₜ[Complex] (n ⊗ₜ[Complex] d)) =
      ((M.regionSubsystem region).complementFactorization
        (M.regionSubsystem (region ∪ M.externalBoundary region))
        (by
          intro site hsite
          exact Finset.mem_union_left _ hsite)).symm
        ((ccomponent.1.restrictScalars Complex).subtype
          (UC.symm (x ⊗ₜ[Complex] n)) ⊗ₜ[Complex] d) := by sorry
