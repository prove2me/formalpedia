-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryToFourFactorReorder_toLinearEquiv_apply_tmul
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundaryToFourFactorReorder_toLinearEquiv_apply_tmul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:24:01.389202+00:00
-- url     : https://prove2.me/theorems/7df64244-9467-4a18-84f4-3e1c7ddbbf07
-- title:
--   BPTCommuting Projector Model: boundary To Four Factor Reorder to Linear Equiv apply tmul
-- statement:
--   The boundary ordering followed by the middle reassociation is the canonical four-factor order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1458-L1468
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1458-L1468

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundaryToFourFactorReorder_toLinearEquiv_apply_tmul
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (a : M.fourFactorA region) (b : M.fourFactorB region)
    (c : M.fourFactorC region) (d : M.fourFactorD region) :
    (M.fourFactorMiddleReassociate region).symm.toLinearEquiv
        ((boundaryToMiddleReorder (M.fourFactorA region) (M.fourFactorB region)
            (M.fourFactorC region) (M.fourFactorD region)).toLinearEquiv
          ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] (a ⊗ₜ[Complex] d))) =
      a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) := by sorry
