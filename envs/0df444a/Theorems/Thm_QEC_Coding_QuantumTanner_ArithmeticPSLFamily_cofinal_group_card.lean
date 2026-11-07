-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLFamily_cofinal_group_card
-- name    : QEC.Coding.QuantumTanner.ArithmeticPSLFamily.cofinal_group_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:01:46.278522+00:00
-- url     : https://prove2.me/theorems/0456151b-43b6-40e1-bf29-83f2f5c7f665
-- title:
--   Arithmetic PSLFamily: cofinal group card
-- statement:
--   Unboundedness follows from an explicit field-to-PSL₂ injection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLFamily.lean#L135-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLFamily.lean#L135-L142

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable (p : ℕ) [hPrime : Fact p.Prime]

variable (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)

theorem QEC.Coding.QuantumTanner.ArithmeticPSLFamily.cofinal_group_card : ∀ N : ℕ, ∃ n, N ≤ Fintype.card (GroupAt p n) := by sorry
