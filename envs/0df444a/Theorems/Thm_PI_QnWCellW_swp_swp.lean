-- Prove2me | Theorems.Thm_PI_QnWCellW_swp_swp
-- name    : PI.QnWCellW.swp_swp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:19:42.267252+00:00
-- url     : https://prove2.me/theorems/213a6b08-c2f5-441e-b434-bcbe1bb12786
-- title:
--   Qn WCell W: swp swp
-- statement:
--   The Qn WCell W construction uses the swp swp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean#L27-L31

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

theorem PI.QnWCellW.swp_swp (k r : ℕ) (p : Fin (2 * r + k + 1)) : swp k r (swp k r p) = p := by sorry
