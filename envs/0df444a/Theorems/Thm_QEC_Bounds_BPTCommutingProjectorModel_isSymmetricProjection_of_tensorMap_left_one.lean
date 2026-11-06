-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_tensorMap_left_one
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_tensorMap_left_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:13.19638+00:00
-- url     : https://prove2.me/theorems/87433a28-7643-4fa0-9d71-f9d3649216a2
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection of tensor Map left one
-- statement:
--   If `P tensor 1` is an orthogonal projection, so is `P`.  A normalized vector
--   of the inert factor reflects both idempotence and self-adjointness.  This is
--   used only for the actual BV03 blocks below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L230-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L230-L269

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_tensorMap_left_one
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (P : Semantics.Operator H) (eta : K) (heta : ‖eta‖ = 1)
    (h : (TensorProduct.map P (1 : Semantics.Operator K)).IsSymmetricProjection) :
    P.IsSymmetricProjection := by sorry
