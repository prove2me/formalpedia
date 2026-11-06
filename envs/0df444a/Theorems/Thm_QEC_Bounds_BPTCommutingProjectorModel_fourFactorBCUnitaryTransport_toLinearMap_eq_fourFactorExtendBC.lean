-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_toLinearMap_eq_fourFactorExtendBC
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_toLinearMap_eq_fourFactorExtendBC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:25:14.259901+00:00
-- url     : https://prove2.me/theorems/f5a902f9-557e-4495-99e2-dd2b29f8eeff
-- title:
--   BPTCommuting Projector Model: four Factor BCUnitary Transport to Linear Map eq four Factor Extend BC
-- statement:
--   The D3/D4 four-factor BC unitary is exactly `fourFactorExtendBC` applied to
--   its physical middle unitary.  This is an equality of maps, not merely an
--   agreement on the active sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L170-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L170-L180

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_toLinearMap_eq_fourFactorExtendBC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (E : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))) :
    (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
      (D := M.fourFactorD region) E).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region E.toLinearEquiv.toLinearMap := by sorry
