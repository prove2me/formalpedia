-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutProjectorMC_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutProjectorMC_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:06.611724+00:00
-- url     : https://prove2.me/theorems/e6cef48e-34b8-42ef-8436-31f9ba9b5fd6
-- title:
--   BPTCommuting Projector Model: first Cut Projector MC is Symmetric Projection
-- statement:
--   The first-cut `MC` projector is an orthogonal projection in its literal coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L320-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L320-L338

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutProjectorMC_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutProjectorMC region).IsSymmetricProjection := by sorry
