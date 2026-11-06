-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_operatorSupportedOnRegister_mul_union
-- name    : QEC.Bounds.BPTCommutingProjectorModel.operatorSupportedOnRegister_mul_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:17:32.79563+00:00
-- url     : https://prove2.me/theorems/d33f30a3-65c2-490c-8607-7e671ffc6243
-- title:
--   BPTCommuting Projector Model: operator Supported On Register mul union
-- statement:
--   Products supported on two regions are supported on their union.  Each factor
--   is lifted through the proved selected-coordinate inclusion before the
--   same-region composition closure is applied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2427-L2443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2427-L2443

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

theorem QEC.Bounds.BPTCommutingProjectorModel.operatorSupportedOnRegister_mul_union
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    {A B : Semantics.Operator L.Register}
    (hA : (M.regionSubsystem left).OperatorSupportedOnRegister A)
    (hB : (M.regionSubsystem right).OperatorSupportedOnRegister B) :
    (M.regionSubsystem (left ∪ right)).OperatorSupportedOnRegister (A * B) := by sorry
