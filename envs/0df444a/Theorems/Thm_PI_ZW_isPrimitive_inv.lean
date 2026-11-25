-- Prove2me | Theorems.Thm_PI_ZW_isPrimitive_inv
-- name    : PI.ZW.isPrimitive_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:45.04505+00:00
-- url     : https://prove2.me/theorems/184a1f23-2ab6-4096-bc12-777075c5a346
-- title:
--   ZW: is Primitive inv
-- statement:
--   The ZW construction uses the is Primitive inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Transfer.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Transfer.lean#L28-L31

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

theorem PI.ZW.isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by sorry
