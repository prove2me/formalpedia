-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exp_quadratic_lower_and_log_linear_lower__a63618dbfd89
-- name    : P2M_GlobalTheory_T_exp_quadratic_lower_and_log_linear_lower__a63618dbfd89
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:22.968517+00:00
-- url     : https://prove2.me/theorems/0aa17b9e-78b0-4cec-b060-d62d81fe1145
-- title:
--   P2 M Global Theory T exp quadratic lower and log linear lower  a63618dbfd89: P2 M Global Theory T exp quadratic lower and log linear lower  a63618dbfd89
-- statement:
--   The P2 M Global Theory T exp quadratic lower and log linear lower  a63618dbfd89 construction uses the P2 M Global Theory T exp quadratic lower and log linear lower  a63618dbfd89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExpQuadraticLowerAndLogLinearLowerStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExpQuadraticLowerAndLogLinearLowerStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpQuadraticLowerAndLogLinearLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpQuadraticLowerAndLogLinearLowerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exp_quadratic_lower_and_log_linear_lower__a63618dbfd89 : (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) := by sorry

alias «GlobalTheory».«T».«exp_quadratic_lower_and_log_linear_lower'» := P2M_GlobalTheory_T_exp_quadratic_lower_and_log_linear_lower__a63618dbfd89
