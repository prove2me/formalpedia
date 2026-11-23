-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_pcoeff1_subst
-- name    : PI.JetsPhW.Low.pcoeff1_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:46.366022+00:00
-- url     : https://prove2.me/theorems/5b62994d-e379-4d27-ad20-7b807a46ab89
-- title:
--   Low: pcoeff1 subst
-- statement:
--   The Low construction uses the pcoeff1 subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L160-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L160-L164

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

theorem PI.JetsPhW.Low.pcoeff1_subst {A : PowerSeries K} (hA : PowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    PowerSeries.coeff 1 (PowerSeries.subst A f : PowerSeries K) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 A := by sorry
