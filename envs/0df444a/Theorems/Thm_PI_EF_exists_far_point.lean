-- Prove2me | Theorems.Thm_PI_EF_exists_far_point
-- name    : PI.EF.exists_far_point
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:46.387579+00:00
-- url     : https://prove2.me/theorems/996f21da-2c48-4e87-97c9-d243333e0ac1
-- title:
--   EF: exists far point
-- statement:
--   The EF construction uses the exists far point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L10-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L10-L52

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

theorem PI.EF.exists_far_point (S : Finset ℝ) (a : ℝ) :
    ∃ x ∈ Set.Icc a (a + 1), ∀ y ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |x - y| := by sorry
