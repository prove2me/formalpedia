-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundarySelectedToBCTransport_toLinearEquiv_apply_basis
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundarySelectedToBCTransport_toLinearEquiv_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:41.643717+00:00
-- url     : https://prove2.me/theorems/eb990b86-4b1a-45aa-80a9-beead8a6088a
-- title:
--   BPTCommuting Projector Model: boundary Selected To BCTransport to Linear Equiv apply basis
-- statement:
--   The selected boundary split is the literal `B tensor C` basis relabeling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1251-L1304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1251-L1304

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundarySelectedToBCTransport_toLinearEquiv_apply_basis
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).selectedDimensions) :
    (M.boundarySelectedToBCTransport region).toLinearEquiv
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.boundary region)).selectedDimensions) Complex labels) =
      M.fourFactorBCoordinateRelabel region
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.internalBoundary region)).selectedDimensions) Complex
          ((M.regionSubsystem (M.internalBoundary region)).splitSelectedLabel
            (M.regionSubsystem (M.boundary region))
            (by
              intro site hsite
              change site ∈ M.boundary region
              rw [M.boundary_eq_internal_union_external region]
              exact Finset.mem_union_left _ hsite)
            labels).1) ⊗ₜ[Complex]
      (quditCoordinateRelabel
          (q := (M.regionSubsystem (M.internalBoundary region)).additionalRetainedDimensions
            (M.regionSubsystem (M.boundary region)))
          (r := (M.regionSubsystem region).additionalRetainedDimensions
            (M.regionSubsystem (region ∪ M.externalBoundary region)))
          (M.boundaryAdditionalCoordinateEquiv region) (by
            intro site
            rfl))
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            ((M.regionSubsystem (M.internalBoundary region)).additionalRetainedDimensions
              (M.regionSubsystem (M.boundary region))))
          Complex
          ((M.regionSubsystem (M.internalBoundary region)).splitSelectedLabel
            (M.regionSubsystem (M.boundary region))
            (by
              intro site hsite
              change site ∈ M.boundary region
              rw [M.boundary_eq_internal_union_external region]
              exact Finset.mem_union_left _ hsite)
            labels).2) := by sorry
