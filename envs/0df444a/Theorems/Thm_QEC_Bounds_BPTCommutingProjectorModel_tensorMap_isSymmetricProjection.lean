-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorMap_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:54.810207+00:00
-- url     : https://prove2.me/theorems/abb0598d-0cc9-4dba-bd5e-86a6195b2545
-- title:
--   BPTCommuting Projector Model: tensor Map is Symmetric Projection
-- statement:
--   Tensoring two orthogonal projections yields an orthogonal projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3779-L3799
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3779-L3799

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorMap_isSymmetricProjection
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    {P : Semantics.Operator H} {Q : Semantics.Operator K}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    (TensorProduct.map P Q).IsSymmetricProjection := by sorry
