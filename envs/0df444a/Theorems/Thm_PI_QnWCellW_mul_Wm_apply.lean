-- Prove2me | Theorems.Thm_PI_QnWCellW_mul_Wm_apply
-- name    : PI.QnWCellW.mul_Wm_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:20:26.890879+00:00
-- url     : https://prove2.me/theorems/7f5e0f70-d8e7-41d3-810a-6575dc32d44b
-- title:
--   Qn WCell W: mul Wm apply
-- statement:
--   The Qn WCell W construction uses the mul Wm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L152-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L152-L166

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

theorem PI.QnWCellW.mul_Wm_apply (k r : ℕ) (c : Fin r → ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (M * Wm k r (Finset.range r) c) p q = M p (swp k r q) * cf k r c (swp k r q) := by sorry
