-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutProjectorAB_isSymmetric
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutProjectorAB_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:17:32.413542+00:00
-- url     : https://prove2.me/theorems/e1d085af-e739-4042-b322-ef924d97b853
-- title:
--   BPTCommuting Projector Model: second Cut Projector AB is Symmetric
-- statement:
--   The literal `AB` projector used by the second cut is symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L378-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L378-L401

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutProjectorAB_isSymmetric
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorProjectorABLocal region).IsSymmetric := by sorry
