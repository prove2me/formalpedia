-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorMiddleReassociate_eq_unitaryLTensor_associator_symm
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorMiddleReassociate_eq_unitaryLTensor_associator_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:25:15.537044+00:00
-- url     : https://prove2.me/theorems/f7e2926e-825c-4696-a1ee-180038d2d9e0
-- title:
--   BPTCommuting Projector Model: four Factor Middle Reassociate eq unitary LTensor associator symm
-- statement:
--   The model's named middle reassociation is definitionally the generic tensor
--   associator transport used by `fourFactorBCUnitaryTransport`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L157-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L157-L163

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorMiddleReassociate_eq_unitaryLTensor_associator_symm
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fourFactorMiddleReassociate region =
      unitaryLTensor (M.fourFactorA region)
        (tensorAssociatorUnitary (M.fourFactorB region)
          (M.fourFactorC region) (M.fourFactorD region)).symm := by sorry
