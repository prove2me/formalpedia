-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_wordPairing_localExtension
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.wordPairing_localExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:10.899028+00:00
-- url     : https://prove2.me/theorems/7d066d4f-20b4-47f1-b3c2-c9d857ecd4bb
-- title:
--   Left Right Cayley Square Complex: word Pairing local Extension
-- statement:
--   Restriction is adjoint to zero extension for the actual coordinate pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L203-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L203-L210

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.wordPairing_localExtension
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) (c : Word (ZMod 2) (A × B)) :
    wordPairing x (X.localExtension vertex c) =
      wordPairing (X.localRestriction vertex x) c := by sorry
