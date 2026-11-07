-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_columnContraction_eq_sum
-- name    : QEC.Coding.QuantumTanner.columnContraction_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:33.725611+00:00
-- url     : https://prove2.me/theorems/1b60a8f6-8130-49f5-9084-40ec0e270435
-- title:
--   Quantum Tanner: column Contraction eq sum
-- statement:
--   The Quantum Tanner construction uses the column Contraction eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L31-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDistance.lean#L31-L35

import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.columnContraction_eq_sum (a : Word F A) (x : Word F (A × B)) :
    columnContraction a x = ∑ i : A, a i • rowRestriction i x := by sorry
