-- Prove2me | Theorems.Thm_PI_ZW_rootNumber_ne_zero
-- name    : PI.ZW.rootNumber_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:05.329576+00:00
-- url     : https://prove2.me/theorems/6db92a27-d5fe-597d-8d83-c752ef406aed
-- title:
--   ZW: root Number ne zero
-- statement:
--   The ZW construction uses the root Number ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Transfer.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Transfer.lean#L33-L43

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

theorem PI.ZW.rootNumber_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    rootNumber χ ≠ 0 := by sorry
