-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_disentangled_of_codeSpace_carrier_eq_bot
-- name    : QEC.Bounds.BPTCommutingProjectorModel.disentangled_of_codeSpace_carrier_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:07.693195+00:00
-- url     : https://prove2.me/theorems/c9d0fe3f-0778-4ba5-a1fa-a019d4e8b3b6
-- title:
--   BPTCommuting Projector Model: disentangled of code Space carrier eq bot
-- statement:
--   The exact BPT conclusion is constructible in the degenerate empty-code case.
--   This isolates the genuinely nontrivial branch for the later finite interaction
--   algebra proof: the zero projector factors through every normalized regional
--   vector and the zero complement projector, with the boundary identity unitary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L88-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L88-L116

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

theorem QEC.Bounds.BPTCommutingProjectorModel.disentangled_of_codeSpace_carrier_eq_bot
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier = ⊥) : M.Disentangled region := by sorry
