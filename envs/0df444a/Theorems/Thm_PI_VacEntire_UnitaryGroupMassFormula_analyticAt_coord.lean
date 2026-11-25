-- Prove2me | Theorems.Thm_PI_VacEntire_UnitaryGroupMassFormula_analyticAt_coord
-- name    : PI.VacEntire.UnitaryGroupMassFormula.analyticAt_coord
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:24.273072+00:00
-- url     : https://prove2.me/theorems/46fc5251-fbba-43d2-82ea-df6a1d9654dd
-- title:
--   Unitary Group Mass Formula: analytic At coord
-- statement:
--   The Unitary Group Mass Formula construction uses the analytic At coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/VacuumEntire/AnalyticAtHfLeft.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/VacuumEntire/AnalyticAtHfLeft.lean#L16-L19

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

theorem PI.VacEntire.UnitaryGroupMassFormula.analyticAt_coord {ι : Type} [Fintype ι] {N N' : ℕ} (τ : ι) (i : Fin N') (j : Fin N)
    (c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (fun z : ι → Fin N' → Fin N → ℂ => z τ i j) c := by sorry
