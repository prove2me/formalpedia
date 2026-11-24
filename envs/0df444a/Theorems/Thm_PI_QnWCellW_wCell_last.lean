-- Prove2me | Theorems.Thm_PI_QnWCellW_wCell_last
-- name    : PI.QnWCellW.wCell_last
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:12.995369+00:00
-- url     : https://prove2.me/theorems/b11d2865-06d7-44bd-8099-5fc5a363f060
-- title:
--   Qn WCell W: w Cell last
-- statement:
--   The Qn WCell W construction uses the w Cell last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L125-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L125-L135

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

theorem PI.QnWCellW.wCell_last (k r : ℕ) (c : Fin r → ℂ) : wCell k r (Fin.last r) c = Wm k r (Finset.range r) c := by sorry
