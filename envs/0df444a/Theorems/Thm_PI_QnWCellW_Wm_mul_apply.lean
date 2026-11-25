-- Prove2me | Theorems.Thm_PI_QnWCellW_Wm_mul_apply
-- name    : PI.QnWCellW.Wm_mul_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:19:22.660965+00:00
-- url     : https://prove2.me/theorems/d5acb423-ca2c-5459-b0c7-f0fcb4b9c683
-- title:
--   Qn WCell W: Wm mul apply
-- statement:
--   The Qn WCell W construction uses the Wm mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L146-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L146-L150

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

theorem PI.QnWCellW.Wm_mul_apply (k r : ℕ) (c : Fin r → ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Wm k r (Finset.range r) c * M) p q = cf k r c p * M (swp k r p) q := by sorry
