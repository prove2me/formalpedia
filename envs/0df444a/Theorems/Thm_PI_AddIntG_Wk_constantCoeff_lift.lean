-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_constantCoeff_lift
-- name    : PI.AddIntG.Wk.constantCoeff_lift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:59.322527+00:00
-- url     : https://prove2.me/theorems/aac60a40-fa6a-5463-b4d6-cabde446b94e
-- title:
--   Wk: constant Coeff lift
-- statement:
--   The Wk construction uses the constant Coeff lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L26-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AddIntG PI.AddIntG.Wk

theorem PI.AddIntG.Wk.constantCoeff_lift {K : Type*} [CommRing K] (S : Subring K) {σ : Type*}
    (g : MvPowerSeries σ S) {c : S} (h : MvPowerSeries.constantCoeff (MvPowerSeries.map S.subtype g) = (c : K)) :
    MvPowerSeries.constantCoeff g = c := by sorry
