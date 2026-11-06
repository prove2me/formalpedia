-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalSelectedFactorization_reorder_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.externalSelectedFactorization_reorder_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:48.614024+00:00
-- url     : https://prove2.me/theorems/bfb630b5-30e1-41b5-a6e4-102243449137
-- title:
--   BPTCommuting Projector Model: external Selected Factorization reorder eq
-- statement:
--   Splitting `M union partialPlus M` first through `partialPlus M`, then
--   relabeling and swapping, is exactly the selected-coordinate factorization
--   through `M`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3281-L3324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3281-L3324

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

theorem QEC.Bounds.BPTCommutingProjectorModel.externalSelectedFactorization_reorder_eq
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    composeUnitaryTransport
      ((M.regionSubsystem (M.externalBoundary region)).selectedFactorization
        (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
          intro site hsite
          exact Finset.mem_union_right _ hsite))
      (M.externalSelectedFactorizationReorder region) =
      (M.regionSubsystem region).selectedFactorization
        (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
          intro site hsite
          exact Finset.mem_union_left _ hsite) := by sorry
