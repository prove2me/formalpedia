-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_apply_basis_eq_fourFactorTransport
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_apply_basis_eq_fourFactorTransport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:52.186571+00:00
-- url     : https://prove2.me/theorems/fefaf139-dbf8-4db1-ba87-e6b2f78b886b
-- title:
--   BPTCommuting Projector Model: boundary Global To Four Factor Transport apply basis eq four Factor Transport
-- statement:
--   The boundary-based coordinate route and the cumulative source route agree on
--   every global computational basis vector.  This is the transport certificate
--   that lets the genuine boundary-overlap support equation be stated on the one
--   canonical four-factor register.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1507-L1570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1507-L1570

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_apply_basis_eq_fourFactorTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label L.localDimension) :
    (M.boundaryGlobalToFourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (M.fourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) := by sorry
