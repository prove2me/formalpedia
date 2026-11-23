-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_coeff_expXY_mul
-- name    : PI.JetsPhW.Low.coeff_expXY_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:42.215296+00:00
-- url     : https://prove2.me/theorems/2e7564f9-bd07-4274-9318-c5fb5e815988
-- title:
--   Low: coeff exp XY mul
-- statement:
--   The Low construction uses the coeff exp XY mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L110-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L110-L137

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

theorem PI.JetsPhW.Low.coeff_expXY_mul {A B : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.coeff bivariateExponentMonomial (A * B) =
      MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B +
        MvPowerSeries.coeff E1 A * MvPowerSeries.coeff E0 B := by sorry
