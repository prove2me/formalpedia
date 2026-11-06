-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unionSelectedFactorization_apply_basis
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unionSelectedFactorization_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:22:22.421596+00:00
-- url     : https://prove2.me/theorems/52a24ffa-f1a2-4d40-ba0e-b28ad771a4d6
-- title:
--   BPTCommuting Projector Model: union Selected Factorization apply basis
-- statement:
--   Basis action of the selected-union factorization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L276-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L276-L294

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.unionSelectedFactorization_apply_basis
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (left ∪ right)).selectedDimensions) :
    M.unionSelectedFactorization left right hdisjoint
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
          Complex labels) =
      (EuclideanSpace.basisFun
        (Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions) Complex
        (M.splitUnionSelectedLabel left right labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions) Complex
        (M.splitUnionSelectedLabel left right labels).2) := by sorry
