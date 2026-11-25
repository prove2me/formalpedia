-- Prove2me | Theorems.Thm_PI_QnWCellW_cN_mk
-- name    : PI.QnWCellW.cN_mk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:44.886502+00:00
-- url     : https://prove2.me/theorems/6f074cb6-0b26-4be0-ab27-75c40bd15085
-- title:
--   Qn WCell W: c N mk
-- statement:
--   The Qn WCell W construction uses the c N mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem PI.QnWCellW.cN_mk (r : ℕ) (c : Fin r → ℂ) (j : ℕ) (h : j < r) : c ⟨j, h⟩ = cN r c j := by sorry
