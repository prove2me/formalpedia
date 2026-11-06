-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToMiddleTransport_conj_extendLocalToRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToMiddleTransport_conj_extendLocalToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:00.005204+00:00
-- url     : https://prove2.me/theorems/d379caab-33ed-4071-9cca-c75b26291e1d
-- title:
--   BPTCommuting Projector Model: boundary Global To Middle Transport conj extend Local To Register
-- statement:
--   Conjugating an arbitrary concrete boundary-local extension through the
--   boundary-based global route produces an identity on `A`, the transported
--   operator on `BC`, and an identity on `D`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1615-L1635
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1615-L1635

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToMiddleTransport_conj_extendLocalToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.boundary region)).selectedSystem) :
    (M.boundaryGlobalToMiddleTransport region).conjOperator
        ((M.regionSubsystem (M.boundary region)).extendLocalToRegister P) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map ((M.boundarySelectedToBCTransport region).conjOperator P)
          (1 : Semantics.Operator (M.fourFactorD region))) := by sorry
