-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitary_conjOperator_eq_of_disjoint_region_support
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitary_conjOperator_eq_of_disjoint_region_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:49.195304+00:00
-- url     : https://prove2.me/theorems/4f954284-13e6-496f-8e84-941a0ee59ce7
-- title:
--   BPTCommuting Projector Model: unitary conj Operator eq of disjoint region support
-- statement:
--   A unitary supported away from a local operator fixes that operator by conjugation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/Support.lean#L77-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/Support.lean#L77-L86

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.unitary_conjOperator_eq_of_disjoint_region_support
    (M : BPTCommutingProjectorModel L kappa) (unitaryRegion operatorRegion : Finset L.Site)
    (hdisjoint : Disjoint unitaryRegion operatorRegion)
    (U : Semantics.UnitaryTransport L.Register L.Register)
    (hU : M.UnitarySupportedOn unitaryRegion U)
    {B : Semantics.Operator L.Register}
    (hB : (M.regionSubsystem operatorRegion).OperatorSupportedOnRegister B) :
    U.conjOperator B = B := by sorry
