-- Prove2me | Theorems.Thm_PI_QnWCellW_cN_val
-- name    : PI.QnWCellW.cN_val
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:45:35.000369+00:00
-- url     : https://prove2.me/theorems/361d9c4b-8bef-4acb-9b68-4e87cb7a99ab
-- title:
--   Qn WCell W: c N val
-- statement:
--   The Qn WCell W construction uses the c N val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L12-L13

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

theorem PI.QnWCellW.cN_val (r : ℕ) (c : Fin r → ℂ) (a : Fin r) : cN r c a.val = c a := by sorry
