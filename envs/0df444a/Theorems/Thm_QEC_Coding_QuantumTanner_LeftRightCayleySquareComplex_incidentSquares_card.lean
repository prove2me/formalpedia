-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_incidentSquares_card
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.incidentSquares_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:55:26.714037+00:00
-- url     : https://prove2.me/theorems/3a36b487-2055-43ed-a15e-c754e84ad062
-- title:
--   Left Right Cayley Square Complex: incident Squares card
-- statement:
--   Every vertex has exactly `|A| |B|` incident squares.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L218-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L218-L222

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_QuantumTanner_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
open QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.incidentSquares_card (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) :
    (Finset.univ.image (X.link vertex)).card = Fintype.card A * Fintype.card B := by sorry
