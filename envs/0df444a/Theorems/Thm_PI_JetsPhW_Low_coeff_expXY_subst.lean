-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_coeff_expXY_subst
-- name    : PI.JetsPhW.Low.coeff_expXY_subst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:28.919493+00:00
-- url     : https://prove2.me/theorems/d372836c-ea9d-4cf3-8831-aa99c12c2003
-- title:
--   Low: coeff exp XY subst
-- statement:
--   The Low construction uses the coeff exp XY subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L151-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L151-L158

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

theorem PI.JetsPhW.Low.coeff_expXY_subst {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff bivariateExponentMonomial (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff bivariateExponentMonomial A +
        PowerSeries.coeff 2 f *
          (2 * (MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 A)) := by sorry
