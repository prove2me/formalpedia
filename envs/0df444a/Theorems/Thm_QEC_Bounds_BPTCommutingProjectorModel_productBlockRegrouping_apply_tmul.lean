-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
-- name    : QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:26:26.144201+00:00
-- url     : https://prove2.me/theorems/3b332a2a-417f-42a5-9fba-85a7bc548038
-- title:
--   BPTCommuting Projector Model: product Block Regrouping apply tmul
-- statement:
--   The BPTCommuting Projector Model construction uses the product Block Regrouping apply tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L49-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L49-L60

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
    {A W N X D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (a : A) (w : W) (n : N) (x : X) (d : D) :
    productBlockRegrouping
      (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] (n ⊗ₜ[Complex] x)) ⊗ₜ[Complex] d) =
      ((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n) ⊗ₜ[Complex] (x ⊗ₜ[Complex] d) := by sorry

attribute [defeq] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
