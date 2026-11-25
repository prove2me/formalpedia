-- Prove2me | Theorems.Thm_PI_EF_four_mul_le_cube
-- name    : PI.EF.four_mul_le_cube
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:41.958996+00:00
-- url     : https://prove2.me/theorems/c11a1d2f-598f-508e-b226-26bc5ed58600
-- title:
--   EF: four mul le cube
-- statement:
--   The EF construction uses the four mul le cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L269-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L269-L271

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

theorem PI.EF.four_mul_le_cube {x : ℝ} (hx : 2 ≤ x) : 4 * x ≤ x ^ 3 := by sorry
