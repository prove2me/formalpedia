-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_SerS_eq_map
-- name    : PI.AddIntG.Wk.SerS_eq_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:53.69098+00:00
-- url     : https://prove2.me/theorems/cd351f94-6328-5a9d-89eb-f157fabaf68e
-- title:
--   Wk: Ser S eq map
-- statement:
--   The Wk construction uses the Ser S eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/SubstMem.lean#L22-L24

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

theorem PI.AddIntG.Wk.SerS_eq_map {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} {f : MvPowerSeries σ K}
    (hf : f ∈ SerS S σ) : ∃ g : MvPowerSeries σ S, MvPowerSeries.map S.subtype g = f := by sorry
