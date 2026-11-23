-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_const_subst
-- name    : PI.JetsPhW.Low.const_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:54.673839+00:00
-- url     : https://prove2.me/theorems/b579bc6e-47d3-4fab-b85a-201f2e03d1a5
-- title:
--   Low: const subst
-- statement:
--   The Low construction uses the const subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L28-L35

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

theorem PI.JetsPhW.Low.const_subst {σ : Type*} {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst A f) = PowerSeries.constantCoeff f := by sorry
