-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_complementPartitionTransport_eq_registerFactorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.complementPartitionTransport_eq_registerFactorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:34.34232+00:00
-- url     : https://prove2.me/theorems/d653c8b7-f234-41cc-9be3-b0ffb16c86e7
-- title:
--   BPTCommuting Projector Model: complement Partition Transport eq register Factorization
-- statement:
--   The complement-first and region-first register factorizations agree on basis labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L942-L969
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L942-L969

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

theorem QEC.Bounds.BPTCommutingProjectorModel.complementPartitionTransport_eq_registerFactorization
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.complementPartitionTransport region =
      (M.regionSubsystem region).registerFactorization := by sorry
