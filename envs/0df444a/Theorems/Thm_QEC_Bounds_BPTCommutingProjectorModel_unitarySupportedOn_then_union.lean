-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitarySupportedOn_then_union
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_then_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:55:21.016033+00:00
-- url     : https://prove2.me/theorems/62fa820b-af58-4714-ab28-6b53a048b6e6
-- title:
--   BPTCommuting Projector Model: unitary Supported On then union
-- statement:
--   Composing units supported on two site regions is supported on their union.
--   This is the support calculation for the source choice
--   `W_{B''C'} U_B^dagger U_C^dagger`: every factor is confined to a piece of
--   the original boundary, hence so is their composition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2475-L2482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2475-L2482

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

theorem QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_then_union
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    {U V : Semantics.UnitaryTransport L.Register L.Register}
    (hU : M.UnitarySupportedOn left U) (hV : M.UnitarySupportedOn right V) :
    M.UnitarySupportedOn (left ∪ right) (thenUnitary U V) := by sorry
