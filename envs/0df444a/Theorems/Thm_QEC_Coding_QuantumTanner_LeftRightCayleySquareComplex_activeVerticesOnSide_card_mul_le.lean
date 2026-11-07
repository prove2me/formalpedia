-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_activeVerticesOnSide_card_mul_le
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.activeVerticesOnSide_card_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:06.837505+00:00
-- url     : https://prove2.me/theorems/4f99ac4a-9f41-4499-b4b5-ee2306ba2487
-- title:
--   Left Right Cayley Square Complex: active Vertices On Side card mul le
-- statement:
--   A lower bound on each nonzero local view bounds the active vertex count.
--   The local-code lower bound is explicit; no expansion estimate is assumed here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L181-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L181-L200

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.activeVerticesOnSide_card_mul_le
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (localDistance : Nat)
    (hlocal : ∀ g, X.localRestriction (g, side) x ≠ 0 →
      localDistance ≤ HammingWeight (X.localRestriction (g, side) x)) :
    localDistance * (X.activeVerticesOnSide side x).card ≤ 2 * HammingWeight x := by sorry
