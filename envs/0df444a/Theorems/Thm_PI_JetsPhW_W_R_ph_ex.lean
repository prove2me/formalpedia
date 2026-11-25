-- Prove2me | Theorems.Thm_PI_JetsPhW_W_R_ph_ex
-- name    : PI.JetsPhW.W.R.ph_ex
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:33:23.038801+00:00
-- url     : https://prove2.me/theorems/b6f48d20-ff96-4147-9dfb-0e04e8551cec
-- title:
--   R: ph ex
-- statement:
--   The R construction uses the ph ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/PolarizationDifferenceFormulaHolds.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/PolarizationDifferenceFormulaHolds.lean#L33-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW
open PI.JetsPhW.W.R
variable {K : Type*} [CommRing K]

theorem PI.JetsPhW.W.R.ph_ex {ex ph : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0) {τ : Type*}
    {s : MvPowerSeries τ K} (hs : MvPowerSeries.constantCoeff s = 0) :
    PowerSeries.subst (PowerSeries.subst s ex) ph =
      PowerSeries.subst s (PowerSeries.subst ex ph : PowerSeries K) := by sorry
