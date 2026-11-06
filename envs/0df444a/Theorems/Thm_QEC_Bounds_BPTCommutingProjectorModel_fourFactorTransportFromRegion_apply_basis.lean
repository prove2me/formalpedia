-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransportFromRegion_apply_basis
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransportFromRegion_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:30.369343+00:00
-- url     : https://prove2.me/theorems/eb645e6b-5cd1-49ad-8553-39493aac464f
-- title:
--   BPTCommuting Projector Model: four Factor Transport From Region apply basis
-- statement:
--   The alternate `AB`-first transport has the same computational-basis action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L547-L608
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L547-L608

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransportFromRegion_apply_basis
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label L.localDimension) :
    M.fourFactorTransportFromRegion region
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.interior region)).selectedDimensions) Complex
          ((M.regionSubsystem (M.interior region)).splitSelectedLabel
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)
            ((M.regionSubsystem region).splitLabel labels).1).1)
        ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            ((M.regionSubsystem (M.interior region)).additionalRetainedDimensions
              (M.regionSubsystem region))) Complex
          ((M.regionSubsystem (M.interior region)).splitSelectedLabel
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)
            ((M.regionSubsystem region).splitLabel labels).1).2)
        ⊗ₜ[Complex]
        ((EuclideanSpace.basisFun
            (Semantics.Qudit.Label
              ((M.regionSubsystem region).additionalRetainedDimensions
                (M.regionSubsystem (region ∪ M.externalBoundary region)))) Complex
            ((M.regionSubsystem region).splitComplementLabel
              (M.regionSubsystem (region ∪ M.externalBoundary region))
              (by
                intro site hsite
                exact Finset.mem_union_left _ hsite)
              ((M.regionSubsystem region).splitLabel labels).2).1)
          ⊗ₜ[Complex]
          (EuclideanSpace.basisFun
            (Semantics.Qudit.Label
              (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
            ((M.regionSubsystem region).splitComplementLabel
              (M.regionSubsystem (region ∪ M.externalBoundary region))
              (by
                intro site hsite
                exact Finset.mem_union_left _ hsite)
              ((M.regionSubsystem region).splitLabel labels).2).2))) := by sorry
