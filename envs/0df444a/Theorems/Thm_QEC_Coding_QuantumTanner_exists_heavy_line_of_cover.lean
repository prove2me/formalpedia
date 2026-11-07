-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_heavy_line_of_cover
-- name    : QEC.Coding.QuantumTanner.exists_heavy_line_of_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:48:26.853222+00:00
-- url     : https://prove2.me/theorems/eeea944a-c315-49c2-8b8a-05ed4544f9b4
-- title:
--   Quantum Tanner: exists heavy line of cover
-- statement:
--   A nonzero covered dual-tensor word has a genuinely heavy row or column.
--   In particular, the edge used to define the opposite set is constructed,
--   not included in the hypotheses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NormalViews.lean#L109-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NormalViews.lean#L109-L147

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.exists_heavy_line_of_cover
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB cutoff : Nat)
    (hA : HasMinimumDistanceAtLeast CA dA)
    (hB : HasMinimumDistanceAtLeast CB dB)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier)
    (hx0 : x ≠ 0) (rows : Finset A) (columns : Finset B)
    (hRows : rows.card < dA) (hColumns : columns.card < dB)
    (hCovered : SupportCovered x rows columns)
    (hCutoffRow : cutoff + columns.card ≤ dB)
    (hCutoffColumn : cutoff + rows.card ≤ dA) :
    (∃ a, cutoff ≤ HammingWeight (rowRestriction a x)) ∨
      ∃ b, cutoff ≤ HammingWeight (columnRestriction b x) := by sorry
