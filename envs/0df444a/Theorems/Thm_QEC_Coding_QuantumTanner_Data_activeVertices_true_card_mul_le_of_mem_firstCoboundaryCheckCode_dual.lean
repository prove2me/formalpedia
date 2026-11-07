-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_activeVertices_true_card_mul_le_of_mem_firstCoboundaryCheckCode_dual
-- name    : QEC.Coding.QuantumTanner.Data.activeVertices_true_card_mul_le_of_mem_firstCoboundaryCheckCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:23:49.927722+00:00
-- url     : https://prove2.me/theorems/b346d40d-d8be-464e-af82-b132c96881a0
-- title:
--   Data: active Vertices true card mul le of mem first Coboundary Check Code dual
-- statement:
--   The symmetric active true-side count uses the two primal-code distances.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L347-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L347-L357

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.activeVertices_true_card_mul_le_of_mem_firstCoboundaryCheckCode_dual
    (D : Data G A B Square XBasis ZBasis) (dA dB : Nat)
    (hA : ∀ a : Word (ZMod 2) A, a ∈ D.codeA.carrier → a ≠ 0 → dA ≤ HammingWeight a)
    (hB : ∀ b : Word (ZMod 2) B, b ∈ D.codeB.carrier → b ≠ 0 → dB ≤ HammingWeight b)
    (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.firstCoboundaryCheckCode.dual.carrier) :
    min dA dB * (D.complex.activeVerticesOnSide true x).card ≤ 2 * HammingWeight x := by sorry
