-- Prove2me | Theorems.Thm_PI_EF_goodHeightExists_of
-- name    : PI.EF.goodHeightExists_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:05.30099+00:00
-- url     : https://prove2.me/theorems/3bf7201a-b08e-4d03-8e59-1c18b95f5714
-- title:
--   EF: good Height Exists of
-- statement:
--   The EF construction uses the good Height Exists of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L273-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L273-L301

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

theorem PI.EF.goodHeightExists_of {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) :
    GoodHeightExists (12 * C + 4) := by sorry
