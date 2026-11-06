-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_scalar_compression_conj_of_disjoint_region_support
-- name    : QEC.Bounds.BPTCommutingProjectorModel.scalar_compression_conj_of_disjoint_region_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:10:52.401957+00:00
-- url     : https://prove2.me/theorems/3c28033d-e9f7-46c7-9b1d-27c503301aa2
-- title:
--   BPTCommuting Projector Model: scalar compression conj of disjoint region support
-- statement:
--   Scalar compression of a local operator is preserved when the code projector is
--   conjugated by a unitary supported on a disjoint region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/Support.lean#L92-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/Support.lean#L92-L117

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

theorem QEC.Bounds.BPTCommutingProjectorModel.scalar_compression_conj_of_disjoint_region_support
    (M : BPTCommutingProjectorModel L kappa) (unitaryRegion operatorRegion : Finset L.Site)
    (hdisjoint : Disjoint unitaryRegion operatorRegion)
    (U : Semantics.UnitaryTransport L.Register L.Register)
    (hU : M.UnitarySupportedOn unitaryRegion U)
    {B : Semantics.Operator L.Register}
    (hB : (M.regionSubsystem operatorRegion).OperatorSupportedOnRegister B)
    {scalar : Complex}
    (hscalar : M.fullCodeProjector * B * M.fullCodeProjector =
      scalar • M.fullCodeProjector) :
    U.conjOperator M.fullCodeProjector * B * U.conjOperator M.fullCodeProjector =
      scalar • U.conjOperator M.fullCodeProjector := by sorry
