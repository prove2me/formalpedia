-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_norm_regionZeroVector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.norm_regionZeroVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:24:18.038085+00:00
-- url     : https://prove2.me/theorems/c94f4380-1bc4-488b-81d7-fed9a17267a4
-- title:
--   BPTCommuting Projector Model: norm region Zero Vector
-- statement:
--   The canonical all-zero regional basis vector has unit norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L66-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L66-L68

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

theorem QEC.Bounds.BPTCommutingProjectorModel.norm_regionZeroVector (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : ‖M.regionZeroVector region‖ = 1 := by sorry
