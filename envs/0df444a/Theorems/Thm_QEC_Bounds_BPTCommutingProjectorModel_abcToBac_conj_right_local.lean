-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_abcToBac_conj_right_local
-- name    : QEC.Bounds.BPTCommutingProjectorModel.abcToBac_conj_right_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:16.004505+00:00
-- url     : https://prove2.me/theorems/64fdccbc-8338-4bbf-a4b7-7e38f659bf06
-- title:
--   BPTCommuting Projector Model: abc To Bac conj right local
-- statement:
--   The `A`/`B` swap sends a right-factor local action to literal left action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L109-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L109-L143

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.abcToBac_conj_right_local
    {A B C : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] (Boperator : Semantics.Operator B) :
    (BPTEntropy.abcToBac A B C).conjOperator
      (TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map Boperator (1 : Semantics.Operator C))) =
      TensorProduct.map Boperator
        (TensorProduct.map (1 : Semantics.Operator A) (1 : Semantics.Operator C)) := by sorry
