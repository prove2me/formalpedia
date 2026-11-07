-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_tensorPuncture_loss_le
-- name    : QEC.Coding.QuantumTanner.hammingWeight_tensorPuncture_loss_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:49:28.543825+00:00
-- url     : https://prove2.me/theorems/07fce6b7-ccd4-4ff1-bdee-59f2b3a21384
-- title:
--   Quantum Tanner: hamming Weight tensor Puncture loss le
-- statement:
--   The deleted rectangle costs at most one full row or column per puncture.
--   Overlaps are counted only once on the left and may be counted twice in the bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L90-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L90-L131

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.hammingWeight_tensorPuncture_loss_le [DecidableEq F]
    (removedA : Finset A) (removedB : Finset B) (x : Word F (A × B)) :
    HammingWeight x ≤ HammingWeight (tensorPunctureMap removedA removedB x) +
      removedA.card * Fintype.card B + Fintype.card A * removedB.card := by sorry
