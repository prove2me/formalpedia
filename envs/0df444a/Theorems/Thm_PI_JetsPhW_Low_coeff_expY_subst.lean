-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_coeff_expY_subst
-- name    : PI.JetsPhW.Low.coeff_expY_subst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:55.722504+00:00
-- url     : https://prove2.me/theorems/60d2c533-ff83-41b9-8291-f959087eaa82
-- title:
--   Low: coeff exp Y subst
-- statement:
--   The Low construction uses the coeff exp Y subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L145-L149

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]

theorem PI.JetsPhW.Low.coeff_expY_subst {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff E1 (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff E1 A := by sorry
