-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_internalBoundaryLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_internalBoundaryLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:52.232207+00:00
-- url     : https://prove2.me/theorems/c40f7d27-2256-4c5a-b1a3-3f6b569a7635
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj internal Boundary Lift
-- statement:
--   In canonical four-factor coordinates, a physical internal-boundary lift is
--   exactly the virtual `B` lift with identities on `A`, `C`, and `D`.  The proof
--   keeps the physical support visible through the boundary factorization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3577-L3637
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3577-L3637

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_internalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.fourFactorTransport region).conjOperator
      ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region)))) := by sorry
