-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutProjectorMC_isSymmetric
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutProjectorMC_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:15:40.879249+00:00
-- url     : https://prove2.me/theorems/a09c04d9-6708-47be-b807-39f191e200f4
-- title:
--   BPTCommuting Projector Model: first Cut Projector MC is Symmetric
-- statement:
--   The literal first-cut `MC` source projector is symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3129-L3151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3129-L3151

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutProjectorMC_isSymmetric
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutProjectorMC region).IsSymmetric := by sorry
