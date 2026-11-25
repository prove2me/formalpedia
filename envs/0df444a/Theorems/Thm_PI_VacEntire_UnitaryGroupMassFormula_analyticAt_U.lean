-- Prove2me | Theorems.Thm_PI_VacEntire_UnitaryGroupMassFormula_analyticAt_U
-- name    : PI.VacEntire.UnitaryGroupMassFormula.analyticAt_U
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:21.58306+00:00
-- url     : https://prove2.me/theorems/c5cabf8e-597a-421c-952d-724a5ff11a3d
-- title:
--   Unitary Group Mass Formula: analytic At U
-- statement:
--   The Unitary Group Mass Formula construction uses the analytic At U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/VacuumEntire/AnalyticAtHfLeft.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/VacuumEntire/AnalyticAtHfLeft.lean#L31-L41

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

theorem PI.VacEntire.UnitaryGroupMassFormula.analyticAt_U {ι : Type} [Fintype ι] {N N' : ℕ} (A : ℝ)
    (x : ι → Fin N' → Fin N → ℂ) (G : (ι → Fin N' → Fin N → ℂ) → ℂ)
    (hG : AnalyticOnNhd ℂ G Set.univ) (c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (U A x G) c := by sorry
