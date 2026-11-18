-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeSelectedEmbeddingCore_apply_tmul
-- name    : QEC.Bounds.BPTCommutingProjectorModel.activeSelectedEmbeddingCore_apply_tmul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T00:00:27.578685+00:00
-- url     : https://prove2.me/theorems/f3ffacd6-8960-4e79-9187-0fa903860390
-- title:
--   BPTCommuting Projector Model: active Selected Embedding Core apply tmul
-- statement:
--   The selected embedding on a pure active-sector tensor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/SelectedEmbeddingCore.lean#L53-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/SelectedEmbeddingCore.lean#L53-L76

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_SelectedEmbeddingCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.activeSelectedEmbeddingCore_apply_tmul
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {nB : Nat} [NeZero nB]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (a : M.fourFactorA region) (w : WB.restrictScalars Complex)
    (n : isotypicLiftedMultiplicity.{0} nB) :
    M.activeSelectedEmbeddingCore region bcomponent WB UB
        ((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n) =
      ((M.regionSubsystem (M.interior region)).selectedFactorization
        (M.regionSubsystem region)
        (by
          intro site hsite
          exact (Finset.mem_sdiff.mp hsite).1)).symm
        (a ⊗ₜ[Complex]
          (bcomponent.1.restrictScalars Complex).subtype
            (UB.symm (w ⊗ₜ[Complex] n))) := by sorry
