-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_coeff_expX_subst
-- name    : PI.JetsPhW.Low.coeff_expX_subst
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:48.922702+00:00
-- url     : https://prove2.me/theorems/cd589c2b-12da-48cb-909f-acf524122a27
-- title:
--   Low: coeff exp X subst
-- statement:
--   The Low construction uses the coeff exp X subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L139-L143

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

theorem PI.JetsPhW.Low.coeff_expX_subst {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff E0 (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff E0 A := by sorry
