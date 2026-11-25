-- Prove2me | Theorems.Thm_PI_JetsPhW_Ch_pderiv_subst_X_ne
-- name    : PI.JetsPhW.Ch.pderiv_subst_X_ne
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:10:26.989643+00:00
-- url     : https://prove2.me/theorems/05fa56b0-2bc3-4c2d-a07a-7236bd7a6f3b
-- title:
--   Ch: pderiv subst X ne
-- statement:
--   The Ch construction uses the pderiv subst X ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffPowEqZeroOfDegreeLt.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffPowEqZeroOfDegreeLt.lean#L90-L93

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

theorem PI.JetsPhW.Ch.pderiv_subst_X_ne {i j : σ} (h : j ≠ i) (g : PowerSeries R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst (MvPowerSeries.X j) g) = 0 := by sorry
