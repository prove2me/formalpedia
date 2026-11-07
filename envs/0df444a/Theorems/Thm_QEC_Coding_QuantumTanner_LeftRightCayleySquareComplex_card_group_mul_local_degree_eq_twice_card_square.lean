-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_card_group_mul_local_degree_eq_twice_card_square
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.card_group_mul_local_degree_eq_twice_card_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:56:59.383289+00:00
-- url     : https://prove2.me/theorems/7146b0ce-4ac5-4cc2-94fe-a76a4f70aae7
-- title:
--   Left Right Cayley Square Complex: card group mul local degree eq twice card square
-- statement:
--   Counting all incidences on either side gives the actual block-length
--   identity. It follows from the square-complex interface, not a family premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L168-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L168-L172

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.card_group_mul_local_degree_eq_twice_card_square
    (X : LeftRightCayleySquareComplex G A B Square) :
    Fintype.card G * (Fintype.card A * Fintype.card B) = 2 * Fintype.card Square := by sorry
