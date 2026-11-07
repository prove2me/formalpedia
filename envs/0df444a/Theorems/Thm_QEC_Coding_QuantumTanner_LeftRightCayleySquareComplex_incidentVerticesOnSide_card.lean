-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_incidentVerticesOnSide_card
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.incidentVerticesOnSide_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:14:06.523135+00:00
-- url     : https://prove2.me/theorems/b4242a07-7dc3-40b9-aa9b-b2bca2c99c32
-- title:
--   Left Right Cayley Square Complex: incident Vertices On Side card
-- statement:
--   Exactly two vertices on either side are incident to each square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L225-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L225-L242

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.incidentVerticesOnSide_card (X : LeftRightCayleySquareComplex G A B Square)
    (square : Square) (side : Bool) :
    (Finset.univ.filter fun g => X.Incident (g, side) square).card = 2 := by sorry
