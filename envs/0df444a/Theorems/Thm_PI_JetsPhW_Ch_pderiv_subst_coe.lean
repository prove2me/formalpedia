-- Prove2me | Theorems.Thm_PI_JetsPhW_Ch_pderiv_subst_coe
-- name    : PI.JetsPhW.Ch.pderiv_subst_coe
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:13:07.1967+00:00
-- url     : https://prove2.me/theorems/cc39cd51-aecc-4c0e-92ad-71663490599e
-- title:
--   Ch: pderiv subst coe
-- statement:
--   The Ch construction uses the pderiv subst coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffPowEqZeroOfDegreeLt.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffPowEqZeroOfDegreeLt.lean#L52-L59

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.JetsPhW
open PI PI.JetsPhW PI.JetsPhW.Ch
variable {R : Type*} [CommRing R] {σ : Type*}

theorem PI.JetsPhW.Ch.pderiv_subst_coe (i : σ) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (q : Polynomial R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst a (q : PowerSeries R)) =
      MvPowerSeries.pderiv R i a * PowerSeries.subst a (dX (q : PowerSeries R)) := by sorry
