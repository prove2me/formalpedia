-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_selectedFactorization_conj_liftExternalBoundary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.selectedFactorization_conj_liftExternalBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:26:30.456056+00:00
-- url     : https://prove2.me/theorems/e054c0d0-632f-4644-8ee8-2568987c4c43
-- title:
--   BPTCommuting Projector Model: selected Factorization conj lift External Boundary
-- statement:
--   An external-boundary local operator, pulled back along the physical-to-virtual
--   `C` relabeling, becomes `1_M tensor Z` when `M union partialPlus M` is split
--   through `M`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3331-L3357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3331-L3357

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

theorem QEC.Bounds.BPTCommutingProjectorModel.selectedFactorization_conj_liftExternalBoundary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    ((M.regionSubsystem region).selectedFactorization
      (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
        intro site hsite
        exact Finset.mem_union_left _ hsite)).conjOperator
      (liftLocalToLarger (M.regionSubsystem (M.externalBoundary region))
        (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
          intro site hsite
          exact Finset.mem_union_right _ hsite)
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem) Z := by sorry
