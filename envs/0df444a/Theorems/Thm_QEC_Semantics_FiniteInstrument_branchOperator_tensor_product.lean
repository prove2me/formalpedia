-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_tensor_product
-- name    : QEC.Semantics.FiniteInstrument.branchOperator_tensor_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:44.533254+00:00
-- url     : https://prove2.me/theorems/4ca1bad9-55da-454a-9644-fc6356204b75
-- title:
--   Finite Instrument: branch Operator tensor product
-- statement:
--   An observed tensor-product branch operator factors exactly on a literal
--   tensor-product input operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L198-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L198-L233

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable {κ' : Type x} [Fintype κ']
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

theorem QEC.Semantics.FiniteInstrument.branchOperator_tensor_product
    (I : FiniteInstrument κ Ω H K) (J : FiniteInstrument κ' Ω' R S)
    (A : Operator H) (B : Operator R)
    (leftOutcome : Ω) (rightOutcome : Ω') :
    (I.tensor J).branchOperator (leftOutcome, rightOutcome)
        (TensorProduct.map A B) =
      TensorProduct.map (I.branchOperator leftOutcome A)
        (J.branchOperator rightOutcome B) := by sorry
