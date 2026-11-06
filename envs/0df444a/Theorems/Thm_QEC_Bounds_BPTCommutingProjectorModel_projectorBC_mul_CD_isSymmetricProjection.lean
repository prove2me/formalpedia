-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorBC_mul_CD_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorBC_mul_CD_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:23.289367+00:00
-- url     : https://prove2.me/theorems/d122c33b-2cdc-4138-8d81-8a7cb57c2900
-- title:
--   BPTCommuting Projector Model: projector BC mul CD is Symmetric Projection
-- statement:
--   The `B bar(M)` source grouped projector is an actual orthogonal projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2612-L2618
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2612-L2618

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorBC_mul_CD_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.projectorBC region * M.projectorCD region).IsSymmetricProjection := by sorry
