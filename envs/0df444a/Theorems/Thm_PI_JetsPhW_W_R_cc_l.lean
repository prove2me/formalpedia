-- Prove2me | Theorems.Thm_PI_JetsPhW_W_R_cc_l
-- name    : PI.JetsPhW.W.R.cc_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:49.667411+00:00
-- url     : https://prove2.me/theorems/b28b23db-cf90-4191-ab2a-ff8c16ea5256
-- title:
--   R: cc l
-- statement:
--   The R construction uses the cc l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/PolarizationDifferenceFormulaHolds.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/PolarizationDifferenceFormulaHolds.lean#L13-L23

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

theorem PI.JetsPhW.W.R.cc_l {l ex : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by sorry
