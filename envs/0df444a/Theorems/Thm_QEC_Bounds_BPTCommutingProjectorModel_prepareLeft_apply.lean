-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_prepareLeft_apply
-- name    : QEC.Bounds.BPTCommutingProjectorModel.prepareLeft_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:31:09.77637+00:00
-- url     : https://prove2.me/theorems/6b5569db-7162-4d5f-93b6-3a13139489db
-- title:
--   BPTCommuting Projector Model: prepare Left apply
-- statement:
--   The left preparation channel is exactly tensoring with its input density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L157-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L157-L188

import Definitions.Def_QEC_Bounds_BPTDisentangling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.prepareLeft_apply (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (A : Operator K) :
    prepareLeft H K rho A = TensorProduct.map rho.toOperator A := by sorry
