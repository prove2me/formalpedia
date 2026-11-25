-- Prove2me | Theorems.Thm_PI_HookSteps_Ioi_eq_filter
-- name    : PI.HookSteps.Ioi_eq_filter
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:44.280256+00:00
-- url     : https://prove2.me/theorems/82fb76d6-6800-5f99-b9d2-561ce4770590
-- title:
--   Hook Steps: Ioi eq filter
-- statement:
--   The Hook Steps construction uses the Ioi eq filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/HookNorm.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/HookNorm.lean#L29-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HookNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps

theorem PI.HookSteps.Ioi_eq_filter {m : ℕ} (x : Fin m) : Finset.Ioi x = Finset.univ.filter (fun j => x < j) := by sorry
