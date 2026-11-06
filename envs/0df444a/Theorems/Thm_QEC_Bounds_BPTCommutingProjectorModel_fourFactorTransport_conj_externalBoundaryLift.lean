-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_externalBoundaryLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_externalBoundaryLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:18:27.23779+00:00
-- url     : https://prove2.me/theorems/29a89d8a-dfbe-4374-a6f3-ad9e3ef19b79
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj external Boundary Lift
-- statement:
--   In the canonical four-factor coordinates, a physical external-boundary lift
--   is exactly the virtual `C` lift with identities on `A`, `B`, and `D`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3493-L3536
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3493-L3536

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_externalBoundaryLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (M.fourFactorTransport region).conjOperator
      ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region))) ) := by sorry
