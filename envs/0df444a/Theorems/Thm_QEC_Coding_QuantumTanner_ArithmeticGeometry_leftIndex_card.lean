-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticGeometry_leftIndex_card
-- name    : QEC.Coding.QuantumTanner.ArithmeticGeometry.leftIndex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:20:29.924013+00:00
-- url     : https://prove2.me/theorems/45a2a284-008f-4962-bcb5-c4fd76da7904
-- title:
--   Arithmetic Geometry: left Index card
-- statement:
--   The Arithmetic Geometry construction uses the left Index card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticGeometry.lean#L66-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticGeometry.lean#L66-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticGeometry
open QEC.Coding.ExpanderCodes.QuaternionGenerators
universe v
variable {F K : Type v} [Field F] [Field K] [Fintype K]

theorem QEC.Coding.QuantumTanner.ArithmeticGeometry.leftIndex_card (f : F →+* K) (epsilon : F) (y : K) [Fintype F]
    (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Fintype.card (LeftIndex f epsilon y hY hOne) = Fintype.card F + 1 := by sorry
