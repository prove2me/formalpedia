-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_tensor_product
-- name    : QEC.Semantics.FiniteInstrument.rawBranchOperator_tensor_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:45.050318+00:00
-- url     : https://prove2.me/theorems/3e184111-c5c0-463d-93c9-5779e8c3df60
-- title:
--   Finite Instrument: raw Branch Operator tensor product
-- statement:
--   A literal tensor-product raw Kraus branch factors as the tensor product
--   of the two component raw branch operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L185-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L185-L194

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

theorem QEC.Semantics.FiniteInstrument.rawBranchOperator_tensor_product
    (I : FiniteInstrument κ Ω H K) (J : FiniteInstrument κ' Ω' R S)
    (A : Operator H) (B : Operator R) (leftIndex : κ) (rightIndex : κ') :
    (I.tensor J).rawBranchOperator (leftIndex, rightIndex)
        (TensorProduct.map A B) =
      TensorProduct.map (I.rawBranchOperator leftIndex A)
        (J.rawBranchOperator rightIndex B) := by sorry
