-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryComplementToADTransport_toLinearEquiv_apply_basis
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryComplementToADTransport_toLinearEquiv_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:43.1922+00:00
-- url     : https://prove2.me/theorems/e99508d1-9237-42cc-991a-c0cca05b7aad
-- title:
--   BPTCommuting Projector Model: boundary Complement To ADTransport to Linear Equiv apply basis
-- statement:
--   The complementary boundary split is the literal `A tensor D` basis relabeling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1307-L1364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1307-L1364

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_eq_internal_union_external

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryComplementToADTransport_toLinearEquiv_apply_basis
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).complementDimensions) :
    (M.boundaryComplementToADTransport region).toLinearEquiv
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.boundary region)).complementDimensions) Complex labels) =
      (quditCoordinateRelabel
          (q := (M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
            (M.regionSubsystem (region ∪ M.externalBoundary region)))
          (r := (M.regionSubsystem (M.interior region)).selectedDimensions)
          (M.boundaryComplementAdditionalCoordinateEquiv region) (by
            intro site
            rfl))
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            ((M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
              (M.regionSubsystem (region ∪ M.externalBoundary region))))
          Complex
          ((M.regionSubsystem (M.boundary region)).splitComplementLabel
            (M.regionSubsystem (region ∪ M.externalBoundary region))
            (by
              intro site hsite
              change site ∈ region ∪ M.externalBoundary region
              rw [M.boundary_eq_internal_union_external region] at hsite
              rcases Finset.mem_union.mp hsite with hinternal | hexternal
              · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
              · exact Finset.mem_union_right _ hexternal)
            labels).1) ⊗ₜ[Complex]
      EuclideanSpace.basisFun
        (Semantics.Qudit.Label
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
        ((M.regionSubsystem (M.boundary region)).splitComplementLabel
          (M.regionSubsystem (region ∪ M.externalBoundary region))
          (by
            intro site hsite
            change site ∈ region ∪ M.externalBoundary region
            rw [M.boundary_eq_internal_union_external region] at hsite
            rcases Finset.mem_union.mp hsite with hinternal | hexternal
            · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
            · exact Finset.mem_union_right _ hexternal)
          labels).2 := by sorry
