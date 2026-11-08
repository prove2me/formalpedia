-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticGeometry_rightIndex_card
-- name    : QEC.Coding.QuantumTanner.ArithmeticGeometry.rightIndex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:20:49.842026+00:00
-- url     : https://prove2.me/theorems/6213a327-217d-4cc0-bd7a-d1b4ea4e5400
-- title:
--   Arithmetic Geometry: right Index card
-- statement:
--   The Arithmetic Geometry construction uses the right Index card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticGeometry.lean#L73-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticGeometry.lean#L73-L78

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticGeometry
open QEC.Coding.ExpanderCodes.QuaternionGenerators
universe v
variable {F K : Type v} [Field F] [Field K] [Fintype K]

theorem QEC.Coding.QuantumTanner.ArithmeticGeometry.rightIndex_card (f : F →+* K) (epsilon : F) (y : K) [Fintype F]
    (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Fintype.card (RightIndex f epsilon y hEpsilon hY hOne) = Fintype.card F + 1 := by sorry
