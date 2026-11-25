-- Prove2me | Theorems.Thm_PI_JetsPhW_Ch_pderiv_subst_X_self
-- name    : PI.JetsPhW.Ch.pderiv_subst_X_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:38.308466+00:00
-- url     : https://prove2.me/theorems/65e94629-75b7-4197-93b1-cb6d662f83ef
-- title:
--   Ch: pderiv subst X self
-- statement:
--   The Ch construction uses the pderiv subst X self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffPowEqZeroOfDegreeLt.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffPowEqZeroOfDegreeLt.lean#L84-L88

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

theorem PI.JetsPhW.Ch.pderiv_subst_X_self (i : σ) (g : PowerSeries R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst (MvPowerSeries.X i) g) =
      PowerSeries.subst (MvPowerSeries.X i) (dX g) := by sorry
