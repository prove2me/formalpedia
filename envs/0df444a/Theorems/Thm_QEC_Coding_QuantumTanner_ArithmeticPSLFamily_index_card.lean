-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLFamily_index_card
-- name    : QEC.Coding.QuantumTanner.ArithmeticPSLFamily.index_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:02:23.118912+00:00
-- url     : https://prove2.me/theorems/31f88c87-bbcb-4f1a-8a00-e957e0a60205
-- title:
--   Arithmetic PSLFamily: index card
-- statement:
--   The Arithmetic PSLFamily construction uses the index card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLFamily.lean#L130-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLFamily.lean#L130-L132

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable (p : ℕ) [hPrime : Fact p.Prime]

variable (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
include hOdd

theorem QEC.Coding.QuantumTanner.ArithmeticPSLFamily.index_card (hNonSquare : ∀ r : ZMod p, r ^ 2 ≠ epsilon) :
    Fintype.card (TorusIndex epsilon) = p + 1 := by sorry
