-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_row_column_approximations_of_cover
-- name    : QEC.Coding.QuantumTanner.exists_row_column_approximations_of_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:31:44.422031+00:00
-- url     : https://prove2.me/theorems/623c6269-84bc-4b42-bf02-5b50ea27ca79
-- title:
--   Quantum Tanner: exists row column approximations of cover
-- statement:
--   Construct actual local-code approximations, with heavy-edge bounds for
--   each nonzero approximating word. The approximations are not input witnesses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NormalViews.lean#L44-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NormalViews.lean#L44-L104

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.exists_row_column_approximations_of_cover
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB : Nat)
    (hA : HasMinimumDistanceAtLeast CA dA)
    (hB : HasMinimumDistanceAtLeast CB dB)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : rows.card < dA) (hColumns : columns.card < dB)
    (hCovered : SupportCovered x rows columns) :
    ∃ r c : Word (ZMod 2) (A × B),
      r ∈ (rowCode (A := A) CB).carrier ∧
      c ∈ (columnCode (B := B) CA).carrier ∧ x = r + c ∧
      (∀ a, HammingWeight (rowRestriction a x + rowRestriction a r) ≤ columns.card) ∧
      (∀ b, HammingWeight (columnRestriction b x + columnRestriction b c) ≤ rows.card) ∧
      (∀ a, rowRestriction a r ≠ 0 →
        dB ≤ HammingWeight (rowRestriction a x) + columns.card) ∧
      (∀ b, columnRestriction b c ≠ 0 →
        dA ≤ HammingWeight (columnRestriction b x) + rows.card) := by sorry
