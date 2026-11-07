-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_hammingWeight_localRestriction_eq_sum
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.hammingWeight_localRestriction_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:59.401364+00:00
-- url     : https://prove2.me/theorems/22d4a14e-ede4-4831-99ff-02230bcd743c
-- title:
--   Left Right Cayley Square Complex: hamming Weight local Restriction eq sum
-- statement:
--   The local weight counts exactly the nonzero incident global coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L118-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L118-L130

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
open QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.hammingWeight_localRestriction_eq_sum
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) :
    HammingWeight (X.localRestriction vertex x) =
      ∑ q : Square, if x q ≠ 0 ∧ X.Incident vertex q then 1 else 0 := by sorry
