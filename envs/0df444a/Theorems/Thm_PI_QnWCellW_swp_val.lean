-- Prove2me | Theorems.Thm_PI_QnWCellW_swp_val
-- name    : PI.QnWCellW.swp_val
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:54:24.272104+00:00
-- url     : https://prove2.me/theorems/21ae8b18-2f5e-477f-9d03-3bba4551445b
-- title:
--   Qn WCell W: swp val
-- statement:
--   The Qn WCell W construction uses the swp val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L22-L25

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

theorem PI.QnWCellW.swp_val (k r : ℕ) (p : Fin (2 * r + k + 1)) :
    (swp k r p).val = if r ≤ p.val ∧ p.val ≤ r + k then p.val else 2 * r + k - p.val := by sorry
