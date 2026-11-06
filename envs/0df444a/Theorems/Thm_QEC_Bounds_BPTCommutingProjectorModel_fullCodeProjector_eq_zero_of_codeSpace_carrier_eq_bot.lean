-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_eq_zero_of_codeSpace_carrier_eq_bot
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_eq_zero_of_codeSpace_carrier_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:23.835267+00:00
-- url     : https://prove2.me/theorems/c0d6315a-cc55-4a58-a5bf-b4ff67bd2284
-- title:
--   BPTCommuting Projector Model: full Code Projector eq zero of code Space carrier eq bot
-- statement:
--   A BPT model with an empty code carrier has zero full code projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L71-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L71-L80

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_eq_zero_of_codeSpace_carrier_eq_bot
    (M : BPTCommutingProjectorModel L kappa) (hcode : M.codeSpace.carrier = ⊥) :
    M.fullCodeProjector = 0 := by sorry
