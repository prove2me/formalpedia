-- Prove2me | Theorems.Thm_PI_VacEntire_UnitaryGroupMassFormula_analyticAt_Hf_left
-- name    : PI.VacEntire.UnitaryGroupMassFormula.analyticAt_Hf_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:20.273435+00:00
-- url     : https://prove2.me/theorems/3f087f63-7c63-4125-b6dc-5406cadf605f
-- title:
--   Unitary Group Mass Formula: analytic At Hf left
-- statement:
--   The Unitary Group Mass Formula construction uses the analytic At Hf left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/VacuumEntire/AnalyticAtHfLeft.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/VacuumEntire/AnalyticAtHfLeft.lean#L21-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VacEntire
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_VacuumEntire_AnalyticAtHfLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VacEntire PI.VacEntire.UnitaryGroupMassFormula
open PI.VacEntire

theorem PI.VacEntire.UnitaryGroupMassFormula.analyticAt_Hf_left {ι : Type} [Fintype ι] {N N' : ℕ} (A : ℝ)
    (x c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (fun z => Hf A z x) c := by sorry
