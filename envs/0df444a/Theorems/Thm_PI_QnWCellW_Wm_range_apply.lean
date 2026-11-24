-- Prove2me | Theorems.Thm_PI_QnWCellW_Wm_range_apply
-- name    : PI.QnWCellW.Wm_range_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:01:16.485484+00:00
-- url     : https://prove2.me/theorems/526e7ff9-16d6-455d-89b9-c139b4cf017c
-- title:
--   Qn WCell W: Wm range apply
-- statement:
--   The Qn WCell W construction uses the Wm range apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L139-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L139-L144

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
set_option maxHeartbeats 800000

theorem PI.QnWCellW.Wm_range_apply (k r : ℕ) (c : Fin r → ℂ) (p x : Fin (2 * r + k + 1)) :
    Wm k r (Finset.range r) c p x = if x = swp k r p then cf k r c p else 0 := by sorry
