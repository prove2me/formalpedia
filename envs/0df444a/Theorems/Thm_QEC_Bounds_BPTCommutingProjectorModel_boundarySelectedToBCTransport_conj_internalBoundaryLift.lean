-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundarySelectedToBCTransport_conj_internalBoundaryLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundarySelectedToBCTransport_conj_internalBoundaryLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:26:11.369232+00:00
-- url     : https://prove2.me/theorems/deabfd58-9910-4c3c-9f25-2223df6ba732
-- title:
--   BPTCommuting Projector Model: boundary Selected To BCTransport conj internal Boundary Lift
-- statement:
--   Splitting the physical boundary into its internal and external pieces sends an
--   internal-boundary operator to the literal `B tensor 1_C` action.  This is the
--   locality bridge used by the second `AB / B bar(M)` cut.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3543-L3570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3543-L3570

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundarySelectedToBCTransport_conj_internalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.boundarySelectedToBCTransport region).conjOperator
      (liftLocalToLarger (M.regionSubsystem (M.internalBoundary region))
        (M.regionSubsystem (M.boundary region)) (by
          intro site hsite
          rw [M.boundary_eq_internal_union_external region]
          exact Finset.mem_union_left _ hsite)
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorC region)) := by sorry
