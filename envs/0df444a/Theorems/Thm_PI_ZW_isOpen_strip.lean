-- Prove2me | Theorems.Thm_PI_ZW_isOpen_strip
-- name    : PI.ZW.isOpen_strip
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:11.347803+00:00
-- url     : https://prove2.me/theorems/dbf86f84-730f-53de-97b4-bf8a044969b0
-- title:
--   ZW: is Open strip
-- statement:
--   The ZW construction uses the is Open strip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Transfer.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Transfer.lean#L45-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Transfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PI PI.ZW
open DirichletCharacter

theorem PI.ZW.isOpen_strip : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} := by sorry
