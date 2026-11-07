-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_tensor_weight_reduction_of_punctured_approximation
-- name    : QEC.Coding.QuantumTanner.exists_tensor_weight_reduction_of_punctured_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:35:20.227198+00:00
-- url     : https://prove2.me/theorems/de113c5f-735e-4eee-ad76-33bcaf9b6ca5
-- title:
--   Quantum Tanner: exists tensor weight reduction of punctured approximation
-- statement:
--   Construct a reducing full tensor word from punctured robustness and
--   actual close row/column words, paying only the deleted-coordinate budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LocalReduction.lean#L26-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LocalReduction.lean#L26-L54

import Definitions.Def_QEC_Coding_QuantumTanner_TensorApproximation
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.exists_tensor_weight_reduction_of_punctured_approximation
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (removedA : Finset A) (removedB : Finset B)
    (dA dB w : Nat)
    (hA : MinimumDistance (puncturedCode CA removedA) dA)
    (hB : MinimumDistance (puncturedCode CB removedB) dB)
    (hRobust : IsRobust (puncturedCode CA removedA) (puncturedCode CB removedB) w)
    (hBudget : 2 * w ≤ dA * dB)
    (x : Word (ZMod 2) (A × B))
    (C R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB))
    (hC : C ∈ (columnCode (puncturedCode CA removedA)).carrier)
    (hR : R ∈ (rowCode (puncturedCode CB removedB)).carrier)
    (hClose : HammingWeight (tensorPunctureMap removedA removedB x + C) +
      HammingWeight (tensorPunctureMap removedA removedB x + R) ≤ w)
    (hMargin : 3 * (HammingWeight (tensorPunctureMap removedA removedB x + C) +
      HammingWeight (tensorPunctureMap removedA removedB x + R)) +
        2 * (removedA.card * Fintype.card B + Fintype.card A * removedB.card) <
      2 * HammingWeight x) :
    ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (x + c) < HammingWeight x := by sorry
