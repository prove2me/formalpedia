-- Prove2me | Theorems.Thm_PI_FglPtW_Wk_serOver_iff
-- name    : PI.FglPtW.Wk.serOver_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:52.296206+00:00
-- url     : https://prove2.me/theorems/a8b5afbf-a4aa-49dc-a6ae-d589ece77e2d
-- title:
--   Wk: ser Over iff
-- statement:
--   The Wk construction uses the ser Over iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/ConstantCoeffPsubst.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/ConstantCoeffPsubst.lean#L13-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglPtW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffPsubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPtW PI.FglPtW.Wk
open PI.AddIntG.Wk
variable {K : Type*} [CommRing K]

theorem PI.FglPtW.Wk.serOver_iff (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    SerOver S f ↔ f ∈ SerS S σ := by sorry
