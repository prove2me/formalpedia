-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitarySupportedOn_of_subset
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:45:07.11796+00:00
-- url     : https://prove2.me/theorems/347624d6-1203-4ca3-840f-95b376f9f267
-- title:
--   BPTCommuting Projector Model: unitary Supported On of subset
-- statement:
--   Boundary support is monotone along a proved inclusion of concrete site sets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L304-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L304-L310

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

theorem QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_of_subset
    (M : BPTCommutingProjectorModel L kappa) (S T : Finset L.Site)
    {U : Semantics.UnitaryTransport L.Register L.Register}
    (hST : S ⊆ T) (hU : M.UnitarySupportedOn S U) :
    M.UnitarySupportedOn T U := by sorry
