-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_nestedFactorizationRight_conj_externalBoundaryLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.nestedFactorizationRight_conj_externalBoundaryLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:56.99596+00:00
-- url     : https://prove2.me/theorems/137f49d0-ce11-48dd-aa13-c9715fc71edf
-- title:
--   BPTCommuting Projector Model: nested Factorization Right conj external Boundary Lift
-- statement:
--   The global nested `M, C, D` coordinates retain the physical support of an
--   external-boundary local operator while exposing it as `1_M tensor Z tensor
--   1_D`.  This is the locality bridge supplied to external-boundary
--   no-information in the first BV03 decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3365-L3409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3365-L3409

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

theorem QEC.Bounds.BPTCommutingProjectorModel.nestedFactorizationRight_conj_externalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (nestedFactorizationRight (M.regionSubsystem region)
      (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
        intro site hsite
        exact Finset.mem_union_left _ hsite)).conjOperator
      ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)
        (TensorProduct.map Z (1 : Semantics.Operator
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem)) := by sorry
