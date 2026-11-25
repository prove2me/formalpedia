-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_two_mul_le_of_dvd_ne
-- name    : PI.SqfRootsInj.W.two_mul_le_of_dvd_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:08.935162+00:00
-- url     : https://prove2.me/theorems/afd4a644-671f-4ade-a1dc-d6b35363bb0a
-- title:
--   W: two mul le of dvd ne
-- statement:
--   The W construction uses the two mul le of dvd ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L41-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]

theorem PI.SqfRootsInj.W.two_mul_le_of_dvd_ne {J E : ℕ} (hd : J ∣ E) (hne : J ≠ E) (hE : 1 ≤ E) : 2 * J ≤ E := by sorry
