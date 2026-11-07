-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_activeVertices_false_card_mul_le_of_mem_middleBoundaryCode_dual
-- name    : QEC.Coding.QuantumTanner.Data.activeVertices_false_card_mul_le_of_mem_middleBoundaryCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:23:43.723387+00:00
-- url     : https://prove2.me/theorems/f9f54ead-2bd0-4deb-98ea-238f0b340bfc
-- title:
--   Data: active Vertices false card mul le of mem middle Boundary Code dual
-- statement:
--   The active false-side vertex count follows from the two dual-code distance
--   bounds and actual global orthogonality, without an extra local-distance premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L333-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L333-L344

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

theorem QEC.Coding.QuantumTanner.Data.activeVertices_false_card_mul_le_of_mem_middleBoundaryCode_dual
    (D : Data G A B Square XBasis ZBasis) (dA dB : Nat)
    (hA : ∀ a : Word (ZMod 2) A, a ∈ D.codeA.dual.carrier → a ≠ 0 →
      dA ≤ HammingWeight a)
    (hB : ∀ b : Word (ZMod 2) B, b ∈ D.codeB.dual.carrier → b ≠ 0 →
      dB ≤ HammingWeight b)
    (x : Word (ZMod 2) Square) (hx : x ∈ D.chainComplex.middleBoundaryCode.dual.carrier) :
    min dA dB * (D.complex.activeVerticesOnSide false x).card ≤ 2 * HammingWeight x := by sorry
