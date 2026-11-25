-- Prove2me | Theorems.Thm_PI_EF_first_character_sum_nonneg
-- name    : PI.EF.first_character_sum_nonneg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:58.369366+00:00
-- url     : https://prove2.me/theorems/d60dc8b6-b600-4391-8070-7d31d5a08f12
-- title:
--   EF: first character sum nonneg
-- statement:
--   The EF construction uses the first character sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ExplicitFormulaFromGluing.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ExplicitFormulaFromGluing.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
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
open Complex

theorem PI.EF.first_character_sum_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : 0 ≤ S1 χ := by sorry
