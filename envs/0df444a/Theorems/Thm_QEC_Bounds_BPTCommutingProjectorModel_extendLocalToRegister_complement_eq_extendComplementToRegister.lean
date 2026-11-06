-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalToRegister_complement_eq_extendComplementToRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_complement_eq_extendComplementToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:40.51774+00:00
-- url     : https://prove2.me/theorems/1ae58e97-7d6e-4b0a-aea8-acf56547d96b
-- title:
--   BPTCommuting Projector Model: extend Local To Register complement eq extend Complement To Register
-- statement:
--   An operator local on the literal complement `regionᶜ` is exactly an identity
--   on `region` tensored with its explicitly relabeled complement operator.
--   This is the complement-side support transport used by the `CD` equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L976-L1007
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L976-L1007

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

theorem QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_complement_eq_extendComplementToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem regionᶜ).selectedSystem) :
    (M.regionSubsystem regionᶜ).extendLocalToRegister P =
      extendComplementToRegister (M.regionSubsystem region)
        ((M.regionComplementCoordinateRelabel region).conjOperator P) := by sorry
