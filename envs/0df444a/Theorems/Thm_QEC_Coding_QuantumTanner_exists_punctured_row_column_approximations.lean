-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_punctured_row_column_approximations
-- name    : QEC.Coding.QuantumTanner.exists_punctured_row_column_approximations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:32:09.43657+00:00
-- url     : https://prove2.me/theorems/b9c85b8b-986e-44c5-a3a0-c936976bf8dc
-- title:
--   Quantum Tanner: exists punctured row column approximations
-- statement:
--   Per-line attained approximations give two genuine punctured-code words
--   with a total residual budget; no nearest-word oracle is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ViewAssembly.lean#L51-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ViewAssembly.lean#L51-L116

import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.exists_punctured_row_column_approximations
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (removedA : Finset A) (removedB : Finset B)
    (x : Word (ZMod 2) (A × B)) (rowError columnError : Nat)
    (hRows : ∀ a : KeptCoordinate removedA, ∃ r : Word (ZMod 2) B,
      r ∈ CB.carrier ∧ HammingWeight (rowRestriction a.1 x + r) ≤ rowError)
    (hColumns : ∀ b : KeptCoordinate removedB, ∃ c : Word (ZMod 2) A,
      c ∈ CA.carrier ∧ HammingWeight (columnRestriction b.1 x + c) ≤ columnError) :
    ∃ C R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB),
      C ∈ (columnCode (puncturedCode CA removedA)).carrier ∧
      R ∈ (rowCode (puncturedCode CB removedB)).carrier ∧
      HammingWeight (tensorPunctureMap removedA removedB x + C) ≤
        Fintype.card B * columnError ∧
      HammingWeight (tensorPunctureMap removedA removedB x + R) ≤
        Fintype.card A * rowError := by sorry
