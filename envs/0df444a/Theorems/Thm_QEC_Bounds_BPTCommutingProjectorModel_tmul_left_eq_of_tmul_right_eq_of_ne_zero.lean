-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tmul_left_eq_of_tmul_right_eq_of_ne_zero
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tmul_left_eq_of_tmul_right_eq_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:34:31.767611+00:00
-- url     : https://prove2.me/theorems/aade126b-7eca-48dc-8704-0e2f3091902f
-- title:
--   BPTCommuting Projector Model: tmul left eq of tmul right eq of ne zero
-- statement:
--   A nonzero fixed right tensor factor can be cancelled from an equality of pure tensors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L24-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L24-L39

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.tmul_left_eq_of_tmul_right_eq_of_ne_zero
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    {left left' : H} (right : K) (hright : right ≠ 0)
    (h : left ⊗ₜ[Complex] right = left' ⊗ₜ[Complex] right) : left = left' := by sorry
