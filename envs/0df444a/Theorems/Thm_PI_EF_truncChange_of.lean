-- Prove2me | Theorems.Thm_PI_EF_truncChange_of
-- name    : PI.EF.truncChange_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:04.072839+00:00
-- url     : https://prove2.me/theorems/bc5a3a1c-e6f9-4798-b98b-6e83c95f5793
-- title:
--   EF: trunc Change of
-- statement:
--   The EF construction uses the trunc Change of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L303-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L303-L347

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open DirichletCharacter

theorem PI.EF.truncChange_of {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) : TruncChange (4 * C) := by sorry
