-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_prepareLeft_apply_rankOne
-- name    : QEC.Bounds.BPTCommutingProjectorModel.prepareLeft_apply_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:28:01.372228+00:00
-- url     : https://prove2.me/theorems/791d668b-8d2c-4f4c-bddb-8da702786df5
-- title:
--   BPTCommuting Projector Model: prepare Left apply rank One
-- statement:
--   The BPTCommuting Projector Model construction uses the prepare Left apply rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L139-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L139-L154

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

theorem QEC.Bounds.BPTCommutingProjectorModel.prepareLeft_apply_rankOne (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (k l : K) :
    prepareLeft H K rho (InnerProductSpace.rankOne Complex k l).toLinearMap =
      ∑ i, (InnerProductSpace.rankOne Complex
        (densityEnsembleVectors H rho i ⊗ₜ[Complex] k)
        (densityEnsembleVectors H rho i ⊗ₜ[Complex] l)).toLinearMap := by sorry
